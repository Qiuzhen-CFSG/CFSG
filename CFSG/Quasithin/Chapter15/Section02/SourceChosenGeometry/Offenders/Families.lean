module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Definitions
public import Stellmacher.ElementaryAbelianMaxSylowImages

/-!
# The actual minimal quotient-image offender families

The quotient-image order is equivalently inclusion after adjoining the two-core.
This makes inclusion-minimality invariant under H-conjugation. Finite descent
constructs Delta from any maximum elementary subgroup outside the core. Its
conjugacy stability forces a member outside every containing two-subgroup;
Sylow conjugacy also supplies members inside each specified Sylow subgroup.
The actual Sigma image family inherits conjugacy stability.

Source: Aschbacher--Smith, Notation 15.2.9, printed p.1110.
-/

public section
open Subgroup Stellmacher
open CFSG.Quasithin.ChapterD CFSG.Quasithin.ChapterD.UniqueFactor

namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
variable {G : Type*} [Group G]

theorem offenderImage_le_iff {H A B : Subgroup G} (hAH : A ≤ H) (hBH : B ≤ H) :
    offenderImage H A ≤ offenderImage H B ↔ A ≤ B ⊔ twoCoreIn H := by
  unfold offenderImage
  rw [Subgroup.map_le_map_iff, QuotientGroup.ker_mk']
  rw [← map_le_map_iff_of_injective H.subtype_injective, Subgroup.map_sup,
    map_subgroupOf_eq_of_le hAH, map_subgroupOf_eq_of_le hBH]
  rfl

theorem delta_map_of_stable {H A : Subgroup G} (e : G ≃* G)
    (hH : H.map e.toMonoidHom = H)
    (hQ : (twoCoreIn H).map e.toMonoidHom = twoCoreIn H)
    (hA : A ∈ delta H) : A.map e.toMonoidHom ∈ delta H := by
  have hHi : H.map e.symm.toMonoidHom = H := by
    have hm := congrArg (Subgroup.map e.symm.toMonoidHom) hH
    simpa [map_map] using hm.symm
  have hQi : (twoCoreIn H).map e.symm.toMonoidHom = twoCoreIn H :=
    by
      have hm := congrArg (Subgroup.map e.symm.toMonoidHom) hQ
      simpa [map_map] using hm.symm
  have hf : A.map e.toMonoidHom ∈ elementaryAbelianMaxSubgroups H := by
    rw [← hH]
    exact (maxFamily_map_injective_iff e.toMonoidHom e.injective H A).mpr hA.1
  refine ⟨hf, ?_, ?_⟩
  · intro hn
    have hm := map_mono (f := e.symm.toMonoidHom) hn
    rw [hQi, map_map] at hm
    exact hA.2.1 (by simpa using hm)
  · intro B hB hBn hBA
    have hBi : B.map e.symm.toMonoidHom ∈ elementaryAbelianMaxSubgroups H := by
      rw [← hHi]
      exact (maxFamily_map_injective_iff e.symm.toMonoidHom e.symm.injective H B).mpr hB
    have hBin : ¬ B.map e.symm.toMonoidHom ≤ twoCoreIn H := by
      intro hn
      have hm := map_mono (f := e.toMonoidHom) hn
      rw [hQ, map_map] at hm
      exact hBn (by simpa using hm)
    have hle : B.map e.symm.toMonoidHom ≤ A ⊔ twoCoreIn H := by
      have hm := map_mono (f := e.symm.toMonoidHom)
        ((offenderImage_le_iff hB.1 hf.1).mp hBA)
      rw [Subgroup.map_sup, hQi] at hm
      simpa [map_map] using hm
    have hmin := (offenderImage_le_iff hA.1.1 hBi.1).mp
      (hA.2.2 _ hBi hBin ((offenderImage_le_iff hBi.1 hA.1.1).mpr hle))
    apply (offenderImage_le_iff hf.1 hB.1).mpr
    have hm := map_mono (f := e.toMonoidHom) hmin
    rw [Subgroup.map_sup, hQ] at hm
    simpa [map_map] using hm

theorem delta_conjugate {H A : Subgroup G} (hA : A ∈ delta H)
    {g : G} (hg : g ∈ H) : A.map (MulAut.conj g).toMonoidHom ∈ delta H := by
  exact delta_map_of_stable (MulAut.conj g)
    (mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer hg))
    (mem_normalizer_iff_map_conj_eq.mp (twoCore_normalized H hg)) hA

variable [Finite G]

theorem delta_nonempty_of_maximum_outside {H : Subgroup G}
    (hex : ∃ A ∈ elementaryAbelianMaxSubgroups H, ¬ A ≤ twoCoreIn H) :
    (delta H).Nonempty := by
  let D : Set (Subgroup G) := {A | A ∈ elementaryAbelianMaxSubgroups H ∧ ¬ A ≤ twoCoreIn H}
  obtain ⟨A,hA,hmin⟩ := (Set.toFinite D).exists_minimalFor (offenderImage H) D hex
  exact ⟨A,hA.1,hA.2,fun B hB hn hle => hmin ⟨hB,hn⟩ hle⟩

omit [Finite G] in
theorem exists_delta_not_le_sylow {H S : Subgroup G} (hSH : S ≤ H)
    (hS : IsPGroup 2 S) (hne : (delta H).Nonempty) :
    ∃ A ∈ delta H, ¬ A ≤ S := by
  classical
  by_contra! hall
  obtain ⟨A,hA⟩ := hne
  let L := conjugateSpanBy A H
  have hLS : L ≤ S := by
    apply (closure_le _).mpr
    rintro x ⟨g,hg,a,ha,rfl⟩
    exact hall _ (delta_conjugate hA hg) (mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
  have hLH : L ≤ H := hLS.trans hSH
  let : (L.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy A H)
  have hp : IsPGroup 2 (L.subgroupOf H) := (hS.to_le hLS).comap_subtype
  have hLQ : L.subgroupOf H ≤ pCore 2 H := le_sSup ⟨inferInstance,hp⟩
  have hm := map_mono (f := H.subtype) hLQ
  rw [map_subgroupOf_eq_of_le hLH] at hm
  exact hA.2.1 ((le_conjugateSpanBy A H).trans hm)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry

namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

theorem exists_delta_in_sylow {H : Subgroup G} (S : Sylow 2 H)
    (hne : (delta H).Nonempty) :
    ∃ A ∈ delta H, A ≤ (S : Subgroup H).map H.subtype := by
  obtain ⟨A,hA⟩ := hne
  let : IsElementaryAbelian 2 A := hA.1.2.1
  have hp : IsPGroup 2 (A.subgroupOf H) :=
    (IsElementaryAbelian.isPGroup 2 A).comap_subtype
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H P S
  have hPS : (P : Subgroup H).map (MulAut.conj g).toMonoidHom = S := by
    change ((g • P : Sylow 2 H) : Subgroup H) = _
    rw [hg]
  refine ⟨A.map (MulAut.conj (g : G)).toMonoidHom,delta_conjugate hA g.property,?_⟩
  have hm := map_mono (f := H.subtype) ((map_mono hP).trans hPS.le)
  rw [map_map,show H.subtype.comp (MulAut.conj g).toMonoidHom =
    (MulAut.conj (g : G)).toMonoidHom.comp H.subtype from rfl,
    ← map_map,map_subgroupOf_eq_of_le hA.1.1] at hm
  exact hm

omit [Finite G] in
theorem sigma_conjugate {H B : Subgroup G} (hB : B ∈ sigma H)
    {g : G} (hg : g ∈ H) : B.map (MulAut.conj g).toMonoidHom ∈ sigma H := by
  obtain ⟨A,hA,rfl⟩ := hB
  refine ⟨A.map (MulAut.conj g).toMonoidHom,delta_conjugate hA hg,?_⟩
  have hQ : (twoCoreIn H).map (MulAut.conj g).toMonoidHom = twoCoreIn H :=
    mem_normalizer_iff_map_conj_eq.mp (twoCore_normalized H hg)
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,hQ]

omit [Finite G] in
theorem sigma_centralizes_span_of_all_centralize {H V B : Subgroup G}
    (hall : ∀ D ∈ sigma H, D ≤ centralizer (V : Set G)) (hB : B ∈ sigma H) :
    B ≤ centralizer (conjugateSpan H V : Set G) := by
  rw [conjugateSpan_eq]
  apply le_centralizer_iff.mpr
  apply (closure_le _).mpr
  rintro x ⟨g,hg,v,hv,rfl⟩ b hb
  have hc := hall _ (sigma_conjugate hB (H.inv_mem hg))
    (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hb) v hv
  change v * (g⁻¹ * b * g⁻¹⁻¹) = (g⁻¹ * b * g⁻¹⁻¹) * v at hc
  have he := congrArg (fun t : G => g * t * g⁻¹) hc
  simpa only [inv_inv,mul_assoc,mul_inv_cancel_left,inv_mul_cancel_left,
    mul_inv_cancel_right,inv_mul_cancel_right,mul_inv_cancel,mul_one] using he.symm

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
