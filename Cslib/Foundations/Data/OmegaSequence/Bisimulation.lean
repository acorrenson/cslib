/-
Copyright (c) 2026 Arthur Correnson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Correnson
-/

module

public import Cslib.Foundations.Data.OmegaSequence.Defs
public import Cslib.Foundations.Data.OmegaSequence.Init

/-!
# Bisimulation for ω-sequences

Infinite sequences are formalized as `ωSequence α = ℕ → α` ).
One way to prove equality between two sequences `s_1, s_2 : ωSequence α`
is to rely on extentionality: two sequences are equal if they are equal
at every time point `n : ℕ`.
Typically, this is proved by induction on `n : ℕ`.
Another approach is to find a bisimulation relation.

In this file we define bisimilarity for `ωSequence α`, and prove that
bisimilarity is equality.
The benefit of working with bisimilarity is that it enables
proving equality by coinduction (instead of induction).
-/

@[expose] public section

namespace Cslib

namespace ωSequence

/-- The bisimilarity relation between ω-sequences

    Intuitively, two ω-sequences are bisimilar if
    their heads are equal and their tails are also bisimilar.
-/
coinductive bisim {α : Type} : ωSequence α -> ωSequence α -> Prop where
  | intro x xs1 xs2 :
    bisim xs1 xs2 ->
    bisim (x ::ω xs1) (x ::ω xs2)

infixl:80 " ≃ω " => bisim

theorem bisim_cons {α : Type} {x1 x2 : α} {s1 s2 : ωSequence α} :
    (x1 ::ω s1) ≃ω (x2 ::ω s2) -> x1 = x2 ∧ s1 ≃ω s2 := by
  intros heq
  generalize heq1 : x1 ::ω s1 = s1' at heq
  generalize heq2 : x2 ::ω s2 = s2' at heq
  cases heq
  case intro x xsl xsr hbisim =>
    simp [cons_injective2 heq1, cons_injective2 heq2, hbisim]

theorem bisim.refl (s : ωSequence α) :
    s ≃ω s := by
  apply (bisim.coinduct (· = ·))
  case hyp =>
    intros s1 s2 Heq
    exists (head s1), (tail s1), (tail s1)
    grind [cons_head_tail]
  case _ => rfl

theorem bisim.trans {s1 s2 s3 : ωSequence α} :
    s1 ≃ω s2 -> s2 ≃ω s3 -> s1 ≃ω s3 := by
  intros h1 h2
  apply bisim.coinduct (fun s1 s3 => ∃ s2, bisim s1 s2 ∧ bisim s2 s3)
  case hyp =>
    clear s1 s2 s3 h1 h2
    rintro s1 s2 ⟨s3, h1, h2⟩
    rw [<- cons_head_tail s1, <- cons_head_tail s3] at h1
    rw [<- cons_head_tail s2, <- cons_head_tail s3] at h2
    grind [cons_head_tail, bisim_cons h1, bisim_cons h2]
  case _ => grind

theorem bisim.symm {s1 s2 : ωSequence α} :
    s1 ≃ω s2 -> s2 ≃ω s1 := by
  intros hbisim
  apply (bisim.coinduct (fun s1 s2 => s2 ≃ω s1))
  case hyp =>
    clear hbisim
    intros s1 s2 hbisim
    exists (head s1), (tail s1), (tail s2)
    cases hbisim; grind [cons, cons_head_tail]
  case _ => grind

/-- Bisimilarity is an equivalence relation -/
theorem bisim.isEquiv {α : Type} : Equivalence (@bisim α) where
  refl := bisim.refl
  symm := bisim.symm
  trans := bisim.trans

/-- Bisimilarity is stronger than equality -/
theorem bisim.sound {α : Type} {s1 s2 : ωSequence α} :
    s1 ≃ω s2 -> s1 = s2 := by
  intros h
  ext n
  induction n generalizing s1 s2
  case zero =>
    rw [<- cons_head_tail s1, <- cons_head_tail s2] at h
    simp [bisim_cons h]
  case succ n ihn =>
    apply @ihn s1.tail s2.tail
    rw [<- cons_head_tail s1, <- cons_head_tail s2] at h
    simp [bisim_cons h]

/-- Bisimilarity is weaker than equality -/
theorem bisim.complete {α : Type} {s1 s2 : ωSequence α} :
    s1 = s2 -> s1 ≃ω s2 := by
  intro heq; simp [heq, bisim.refl]

theorem bisim.is_equality {α} {s1 s2 : ωSequence α} :
    bisim s1 s2 <-> s1 = s2 := by
  exact ⟨bisim.sound, bisim.complete⟩

end ωSequence

end Cslib
