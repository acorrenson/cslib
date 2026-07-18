/-
Copyright (c) 2026 Arthur Correnson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Correnson
-/

module

public import Cslib.Foundations.Data.OmegaSequence.Defs
public import Cslib.Foundations.Data.OmegaSequence.Init
public import Cslib.Foundations.Data.OmegaSequence.Bisimulation

/-!
# Equality "up to taus" for weak ω-sequences

Sequences of type `ωSequence (Option α)` (i.e., weak streams) are commonly used
when studying the semantics of asynchronous systems.
In this setting, the value `none` (often called `τ`) is used to model internal computation steps.
We often want to consider sequences to be equivalent
even if they are only equal "up to taus".

This file defines `eutt` (equivalence up-to tau), and proves
that it is indeed an equivalence relation.

## References

* [*An equational theory for weak bisimulation (...) *][Zakowski2020]
-/

@[expose] public section

namespace Cslib

namespace ωSequence

open List

/-- Base functor underlying `eutt` -/
inductive euttF {α : Type} (R : ωSequence (Option α) -> ωSequence (Option α) -> Prop) :
  ωSequence (Option α) -> ωSequence (Option α) -> Prop where
  | taul xs1 xs2 :
    -- skip a `τ` on the left (inductively)
    euttF R xs1 xs2 ->
    euttF R (none ::ω xs1) xs2
  | taur xs1 xs2 :
    -- skip a `τ` on the right (inductively)
    euttF R xs1 xs2 ->
    euttF R xs1 (none ::ω xs2)
  | tau xs1 xs2 :
    -- skip two `τ`'s (coinductively)
    R xs1 xs2 ->
    euttF R (none ::ω xs1) (none ::ω xs2)
  | vis x xs1 xs2 :
    -- skip two equal "visible" elements (coinductively)
    R xs1 xs2 ->
    euttF R (some x ::ω xs1) (some x ::ω xs2)

/-- `euttF` is a monotone relation transformer -/
theorem euttF.mono {α} (R1 R2 : ωSequence (Option α) -> ωSequence (Option α) -> Prop):
    (∀ a b, R1 a b -> R2 a b) -> (∀ a b, euttF R1 a b -> euttF R2 a b) := by
  intros h1 a b h2
  induction h2 <;> grind [euttF]

/-- `eutt` is defined coinductively, as the greatest fixpoint of `euttF` -/
inductive eutt (s1 s2 : ωSequence (Option α)) : Prop where
  | coind
    (R : ωSequence (Option α) -> ωSequence (Option α) -> Prop)
    (R_init  : R s1 s2)
    (R_step : ∀ a b, R a b -> euttF R a b)

/-- `eutt` is a postfixpoint of `euttF` -/
theorem eutt.unfold {s1 s2 : ωSequence (Option α)} :
    eutt s1 s2 -> euttF eutt s1 s2 := by
  rintro ⟨R, R_init, R_step⟩
  apply euttF.mono R
  · intros a b hab
    apply (eutt.coind R hab R_step)
  · grind [R_step s1 s2]

/-- `eutt` is a prefixpoint of `euttF` -/
theorem eutt.fold {s1 s2 : ωSequence (Option α)} :
    euttF eutt s1 s2 -> eutt s1 s2 := by
  intro hsim
  apply eutt.coind (euttF eutt)
  <;> grind [euttF.mono eutt, eutt.unfold]

/-- `eutt` is the unique fixpoint of `euttF` -/
theorem eutt.fixpoint :
    @eutt α = @euttF α eutt := by
  ext s1 s2; grind [eutt.fold, eutt.unfold]

theorem eutt.taur {s1 s2 : ωSequence (Option α)} :
    eutt s1 s2 -> eutt s1 (none ::ω s2) := by
  intros h; grind [eutt.unfold, eutt.fold, euttF]

theorem eutt.taul {s1 s2 : ωSequence (Option α)} :
    eutt s1 s2 -> eutt (none ::ω s1) s2 := by
  intros h; grind [eutt.unfold, eutt.fold, euttF]

theorem eutt.tau {s1 s2 : ωSequence (Option α)} :
    eutt s1 s2 -> eutt (none ::ω s1) (none ::ω s2) := by
  intros h; grind [eutt.unfold, eutt.fold, euttF]

theorem eutt.vis {x : α} {s1 s2 : ωSequence (Option α)} :
    eutt s1 s2 -> eutt (some x ::ω s1) (some x ::ω s2) := by
  intros h; grind [eutt.unfold, eutt.fold, euttF]

/-- `eutt` is reflexive -/
theorem eutt.refl (s : ωSequence (Option α)) :
    s.eutt s := by
  apply eutt.coind (· = ·)
  case R_init => rfl
  case R_step =>
    clear s; intros a b heq
    rw [heq, <- cons_head_tail b]
    cases b.head <;> grind [euttF]

/-- `eutt` is symmetric -/
theorem eutt.symm {s1 s2 : ωSequence (Option α)} :
    s1.eutt s2 -> s2.eutt s1 := by
  intros heutt
  apply eutt.coind (flip eutt)
  case R_init => assumption
  case R_step =>
    clear heutt; intros a b hab
    replace hab := eutt.unfold hab
    induction hab <;> grind [euttF, flip]

/-- finite sequence of `τ`'s -/
def taus {α} (n : ℕ) : List (Option α) :=
  replicate n none

@[simp, scoped grind =]
theorem taus_zero {α} :
    @taus α 0 = [] := by
  simp [taus, replicate]

@[simp, scoped grind =]
theorem taus_succ {α} {n : ℕ} :
    @taus α (n + 1) = none :: taus n := by
  simp [taus, replicate]

@[simp, scoped grind =]
theorem taus_add {α} {n m : ℕ} :
    @taus α (n + m) = taus n ++ taus m := by
  simp [taus]

/-- infinite sequence of `τ`'s -/
def ωtaus {α} : ωSequence (Option α) :=
  ωSequence.const none

theorem euttF.taus_l {R} {n : ℕ} {s1 s2 : ωSequence (Option α)} :
    euttF R s1 s2 -> euttF R (taus n ++ω s1) s2 := by
  intros h
  induction n
  case zero => grind
  case succ n ihn => grind [cons_append_ωSequence, euttF.taul]

theorem euttF.taus_r {R} {n : ℕ} {s1 s2 : ωSequence (Option α)} :
    euttF R s1 s2 -> euttF R s1 (taus n ++ω s2) := by
  intros h
  induction n
  case zero => grind
  case succ n ihn => grind [cons_append_ωSequence, euttF.taur]

theorem eutt.taus_l {n : ℕ} {s1 s2 : ωSequence (Option α)} :
    eutt s1 s2 -> eutt (taus n ++ω s1) s2 := by
  grind [euttF.taus_l, eutt.fold, eutt.unfold]

theorem eutt.taus_r {n : ℕ} {s1 s2 : ωSequence (Option α)} :
    eutt s1 s2 -> eutt s1 (taus n ++ω s2) := by
  grind [euttF.taus_r, eutt.fold, eutt.unfold]

theorem eutt.tau_l_inv {s1 s2 : ωSequence (Option α)} :
    eutt (none ::ω s1) s2 -> ∃ n s2', s2 = taus n ++ω s2' ∧ eutt s1 s2' := by
  intros h
  generalize heq : none ::ω s1 = s1_ at h
  replace h := eutt.unfold h
  induction h generalizing s1
  case taul s1' s2' h ih =>
    replace ⟨__, heq⟩ := cons_injective2 heq
    exists 0, s2'
    simp [heq, taus, eutt.fold h]
  case taur s1' s2' h ih =>
    specialize ih heq
    replace ⟨k, s2'', htaus, ih⟩ := ih
    rw [htaus]
    exists (k + 1), s2''
  case tau s1' s2' h =>
    replace ⟨_, heq⟩ := cons_injective2 heq
    exists 1, s2'
    simp [taus, heq, h]
  case vis =>
    replace ⟨hcontr, _⟩ := cons_injective2 heq
    grind

theorem eutt.tau_r_inv {s1 s2 : ωSequence (Option α)} :
    eutt s1 (none ::ω s2) -> ∃ n s1', s1 = taus n ++ω s1' ∧ eutt s1' s2 := by
  grind [eutt.symm, eutt.tau_l_inv]

theorem eutt.taus_l_inv {s1 s2 : ωSequence (Option α)} :
    ∀ n1, eutt (taus n1 ++ω s1) s2 -> ∃ n2 s2', s2 = taus n2 ++ω s2' ∧ eutt s1 s2' := by
  intros n1
  induction n1 generalizing s2
  case zero => grind
  case succ n ih =>
    intros heq
    replace ⟨n2, s2', h2, heq⟩ := eutt.tau_l_inv heq
    have ⟨m2, s2'', ih1, ih2⟩ := ih heq
    exists n2 + m2, s2''
    simp [ih2, h2, ih1]

theorem eutt.taus_r_inv {s1 s2 : ωSequence (Option α)} :
    ∀ n2, eutt s1 (taus n2 ++ω s2) -> ∃ n1 s1', s1 = taus n1 ++ω s1' ∧ eutt s1' s2 := by
  grind [eutt.symm, eutt.taus_l_inv]

theorem eutt.insert_tau_l {s1 s2 : ωSequence (Option α)} :
    eutt (none ::ω s1) s2 -> eutt s1 s2 := by
  intros h
  have ⟨n, s1', h1, h2⟩ := eutt.tau_l_inv h
  simp [h1, eutt.taus_r h2]

theorem eutt.insert_tau_r {s1 s2 : ωSequence (Option α)} :
    eutt s1 (none ::ω s2) -> eutt s1 s2 := by
  intros h
  have ⟨n, s2', h1, h2⟩ := eutt.tau_r_inv h
  simp [h1, eutt.taus_l h2]

theorem eutt.insert_taus_l {s1 s2 : ωSequence (Option α)} :
    ∀ n, eutt (taus n ++ω s1) s2 -> eutt s1 s2 := by
  intros n
  induction n
  case zero => grind
  case succ n ihn =>
    intros h
    apply ihn (eutt.insert_tau_l h)

theorem eutt.insert_taus_r {s1 s2 : ωSequence (Option α)} :
    ∀ n, eutt s1 (taus n ++ω s2) -> eutt s1 s2 := by
  grind [eutt.symm, eutt.insert_taus_l]

theorem eutt.visl_inv {e : α} {s1 s2 : ωSequence (Option α)} :
    eutt (some e ::ω s1) s2 -> ∃ n s2', s2 = taus n ++ω e ::ω s2' ∧ eutt s1 s2' := by
  intros h
  generalize heq : (some e ::ω s1) = s1_ at h
  replace h := eutt.unfold h
  induction h generalizing s1
  case taul s1' s2' h ih => grind [cons_injective2 heq]
  case taur s1' s2' h ih =>
    specialize ih heq
    replace ⟨n, s2'', htaus, ih⟩ := ih
    exists (n + 1), s2''
    simp [taus_succ, htaus, ih, cons_append_ωSequence]
  case tau s1' s2' h => grind [cons_injective2 heq]
  case vis x s1' s2' h =>
    have ⟨heq1, heq2⟩ := cons_injective2 heq
    exists 0, s2'
    simp [taus, heq1, heq2, h]

theorem eutt.visr_inv {e : α} {s1 s2 : ωSequence (Option α)} :
    eutt s1 (some e ::ω s2) -> ∃ n s1', s1 = taus n ++ω e ::ω s1' ∧ eutt s1' s2 := by
  grind [eutt.symm, eutt.visl_inv]

/-- `eutt` is transitive -/
theorem eutt.trans {s1 s2 s3 : ωSequence (Option α)} :
    s1.eutt s2 -> s2.eutt s3 -> s1.eutt s3 := by
  intros h1 h2
  let ch := (fun (s1 s3 : ωSequence (Option α)) => ∃ s2, s1.eutt s2 ∧ s2.eutt s3)
  apply eutt.coind ch
  case R_init => grind
  case R_step =>
    clear * -
    rintro s1 s3 ⟨s2, h1, h2⟩
    replace h1 := eutt.unfold h1
    induction h1
    case taul s1' s2' h1 ih1 => grind [euttF.taul]
    case taur s1' s2' h1 ih1 => grind [eutt.insert_tau_l]
    case tau s1' s2' h1 =>
      rw [<- s3.cons_head_tail] at *
      generalize s3.head = s30 at h2
      cases s30
      case none =>
        grind [eutt.insert_tau_r, eutt.insert_tau_l, euttF.tau]
      case some x =>
        replace h2 := eutt.insert_tau_l h2
        replace ⟨n, s1'', h2, h3⟩ := eutt.visr_inv h2
        rw [h2] at h1
        replace h1 := eutt.insert_taus_r _ h1
        replace ⟨m, s1''', h4, h5⟩ := eutt.visr_inv h1
        rw [h4]
        grind [euttF.taus_l, euttF]
    case vis x s1' s2' h1 =>
      replace ⟨n, s2'', h2, h3⟩ := eutt.visl_inv h2
      rw [h2]
      apply euttF.taus_r
      grind [euttF]

/-- `eutt` is an equivalence -/
theorem eutt.isEquiv {α} : Equivalence (@eutt α) where
  refl := eutt.refl
  symm := eutt.symm
  trans := eutt.trans


/-- a sequence containing at least one `τ` has a first non-`τ` position -/
theorem exists_least_visible {α : Type} {n : ℕ} (s : ωSequence (Option α)) :
    s n ≠ none -> ∃ n x s', s = taus n ++ω some x ::ω s' := by
  intros hne
  induction n generalizing s
  case zero =>
    cases heq : (s 0)
    case none => grind
    case some x => exists 0, x, s.tail; grind
  case succ n ih =>
    cases heq : s 0
    case none =>
      have ⟨m, x, s', hm⟩ := ih s.tail hne
      exists (m + 1), x, s'
      rw [<- cons_head_tail s, head, heq, hm]
      rfl
    case some y => exists 0, y, s.tail; grind

/-- an sequence is either the constant `ωtaus`, or it has a first non-`τ` position -/
theorem ωtaus_or_least_visible {α : Type} (s : ωSequence (Option α)) :
    s = ωtaus ∨ (∃ n x s', s = taus n ++ω some x ::ω s') := by
  cases Classical.em (∃ n x s', s = taus n ++ω some x ::ω s')
  case inl h => grind
  case inr h =>
    left; apply ωSequence.ext
    intros n
    cases heq : (s n)
    case none => rfl
    case some sn =>
      exfalso; apply h; clear h
      have hne : s n ≠ none := by grind
      apply exists_least_visible s hne

theorem ωtaus_unfold {α : Type} :
    ωtaus = none ::ω @ωtaus α := by
  apply const_eq

theorem taus_app_cons_none {s : ωSequence (Option α)} :
    none ::ω (taus n ++ω s) = taus n ++ω (none ::ω s) := by
  induction n generalizing s
  case zero => grind
  case succ n ihn =>
    apply ωSequence.ext; intros k
    cases k
    case zero => simp [taus, replicate]
    case succ i => simp [taus_succ, cons_append_ωSequence, ihn]

theorem eutt.ωtaus_l (s : ωSequence (Option α)) :
    eutt ωtaus s -> s = ωtaus := by
  intros heutt
  apply bisim.sound
  apply bisim.symm
  generalize heq : ωtaus = s' at *
  apply bisim.coind (fun s1 s2 => s1 = ωtaus ∧ eutt ωtaus s2)
  · grind
  · clear * -
    rintro s1 s2 ⟨h1, h2⟩
    rw [<- h1] at h2; rw [ωtaus_unfold] at h1
    simp only [h1, get_zero_cons, tail_cons, true_and]
    rw [<- ωtaus_unfold] at h1
    replace h2 := eutt.unfold h2
    induction h2
    case taul s1' s2' h ih =>
      apply ih
      rw [ωtaus_unfold] at h1
      replace ⟨__, h1⟩ := ωSequence.cons_injective2 h1
      apply h1
    case taur s1' s2' h ih =>
      replace ⟨h1, h2⟩ := ih h1
      simp only [head, get_zero_cons, tail_cons, true_and]
      rw [<- cons_head_tail s2', <- h1]
      grind [eutt.taur]
    case tau s1' s2' h =>
      simp only [get_zero_cons, tail_cons, true_and]
      rw [ωtaus_unfold] at h1
      replace ⟨__, h1⟩ := ωSequence.cons_injective2 h1
      grind
    case vis x s1' s2' h =>
      rw [ωtaus_unfold] at h1
      replace ⟨h1, _⟩ := ωSequence.cons_injective2 h1
      grind

theorem eutt.ωtaus_r (s : ωSequence (Option α)) :
    eutt s ωtaus -> s = ωtaus := by
  grind [eutt.symm, eutt.ωtaus_l]

end ωSequence

end Cslib
