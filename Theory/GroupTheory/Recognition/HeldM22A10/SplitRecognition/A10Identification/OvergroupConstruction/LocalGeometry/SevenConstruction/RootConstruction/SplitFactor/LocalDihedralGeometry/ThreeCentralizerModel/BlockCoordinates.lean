module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.LocalDihedralGeometry.Contracts
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.QuotientRecognition.Model
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.ModelInvolutions
public import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic

/-!
# Block coordinates for the concrete involution centralizers

The even pairs in C_S4((01)(23)) × S_n embed on disjoint letter blocks.
The sign kernel has half the product order, so the embeddings for n = 3, 6
exhaust the actual centralizers in A7 and A10. Both retain the distinguished
double transposition. These coordinates are used for the cubic centralizers.

Source: Held, DOI 10.1215/ijm/1256053756, Lemma 5.4, pp.236–237.
-/

public section

open Subgroup Equiv Equiv.Perm
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry.ThreeCentralizer

@[expose] def dt : Perm (Fin 4) := swap 0 1 * swap 2 3
abbrev Four := centralizer ({dt} : Set (Perm (Fin 4)))
@[expose] def dtFour : Four := ⟨dt, mem_centralizer_singleton_iff.mpr rfl⟩
@[expose] def flip : Four := ⟨swap 0 1, mem_centralizer_singleton_iff.mpr (by decide +kernel)⟩

@[expose] def parity (n : ℕ) : Four × Perm (Fin n) →* ℤˣ :=
  ((sign.comp Four.subtype).comp (MonoidHom.fst _ _)) *
    (sign.comp (MonoidHom.snd _ _))
abbrev Pair (n : ℕ) := (parity n).ker

@[expose] def block (n : ℕ) : Four × Perm (Fin n) →* Perm (Fin (4 + n)) :=
  (Equiv.permCongrHom finSumFinEquiv).toMonoidHom.comp
    ((sumCongrHom _ _).comp (Four.subtype.prodMap (MonoidHom.id _)))

theorem block_sign (n) (x : Four × Perm (Fin n)) : sign (block n x) = parity n x := by
  change sign (finSumFinEquiv.permCongr (Equiv.sumCongr x.1.val x.2)) = _
  rw [sign_permCongr, sign_sumCongr]
  rfl
theorem block_injective (n) : Function.Injective (block n) := by
  intro x y h
  have h1 := (Equiv.permCongrHom finSumFinEquiv).injective h
  have h2 := sumCongrHom_injective h1
  change (x.1.val, x.2) = (y.1.val, y.2) at h2
  exact Prod.ext (Subtype.ext (Prod.mk.inj h2).1) (Prod.mk.inj h2).2

@[expose] def evenBlock (n) : Pair n →* alternatingGroup (Fin (4 + n)) :=
  ((block n).comp (parity n).ker.subtype).codRestrict _ (by
    intro x
    rw [mem_alternatingGroup]
    exact (block_sign n x).trans x.property)

theorem four_card : Nat.card Four = 8 := by
  rw [nat_card_centralizer]
  have h : dt.cycleType = {2, 2} := by decide +kernel
  rw [h]
  norm_num

theorem pair_card (n) : Nat.card (Pair n) * 2 = 8 * n.factorial := by
  have hs : Function.Surjective (parity n) := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one _⟩
    · refine ⟨(flip, 1), ?_⟩
      change sign (swap (0 : Fin 4) 1) * sign (1 : Perm (Fin n)) = -1
      simp
  have h := (parity n).ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr hs, card_top,
    Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int,
    Nat.card_prod, four_card, Nat.card_eq_fintype_card (α := Perm (Fin n)),
    Fintype.card_perm, Fintype.card_fin] at h
  exact h

theorem block_dt (n) (x : Four × Perm (Fin n)) :
    Commute (block n x) (block n (dtFour, 1)) := by
  apply Commute.map
  exact Prod.ext (Subtype.ext (mem_centralizer_singleton_iff.mp x.1.property))
    (mul_one x.2 |>.trans (one_mul x.2).symm)

theorem block_dt_six : block 6 (dtFour, 1) = (doubleTransposition : Perm (Fin 10)) := by
  decide +kernel
theorem block_dt_three : block 3 (dtFour, 1) = (sevenInvolution : Perm (Fin 7)) := by
  decide +kernel

@[expose] def muHom : Pair 6 →* MuModel :=
  (evenBlock 6).codRestrict _ (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    change block 6 x.val * (doubleTransposition : Perm (Fin 10)) =
      (doubleTransposition : Perm (Fin 10)) * block 6 x.val
    simpa only [block_dt_six] using (block_dt 6 x).eq)

@[expose] def sevenHom : Pair 3 →* sevenInvolutionCentralizer :=
  (evenBlock 3).codRestrict _ (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    change block 3 x.val * (sevenInvolution : Perm (Fin 7)) =
      (sevenInvolution : Perm (Fin 7)) * block 3 x.val
    simpa only [block_dt_three] using (block_dt 3 x).eq)

theorem muHom_injective : Function.Injective muHom := by
  intro x y h
  exact Subtype.ext (block_injective 6 (congrArg (fun z : MuModel => z.val.val) h))
theorem sevenHom_injective : Function.Injective sevenHom := by
  intro x y h
  exact Subtype.ext (block_injective 3 (congrArg (fun z : sevenInvolutionCentralizer => z.val.val) h))
@[expose] noncomputable def muEquiv : Pair 6 ≃* MuModel :=
  MulEquiv.ofBijective muHom (muHom_injective.bijective_of_nat_card_le (by
    have h := pair_card 6
    rw [centralizer_noncentral_card]
    norm_num only [Nat.factorial] at h
    omega))
@[expose] noncomputable def sevenEquiv : Pair 3 ≃* sevenInvolutionCentralizer :=
  MulEquiv.ofBijective sevenHom (sevenHom_injective.bijective_of_nat_card_le (by
    have h := pair_card 3
    rw [QuotientRecognition.Model.centralizer_card]
    norm_num only [Nat.factorial] at h
    omega))

@[expose] def muPair (n) : Pair n := ⟨(dtFour, 1), by
  change sign dt * sign (1 : Perm (Fin n)) = 1
  simp [dt]⟩
theorem muEquiv_mark : muEquiv (muPair 6) = modelMu := by
  apply Subtype.ext
  exact Subtype.ext block_dt_six
theorem sevenEquiv_mark : sevenEquiv (muPair 3) = sevenCentralInvolution := by
  apply Subtype.ext
  exact Subtype.ext block_dt_three
end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.LocalDihedralGeometry.ThreeCentralizer
