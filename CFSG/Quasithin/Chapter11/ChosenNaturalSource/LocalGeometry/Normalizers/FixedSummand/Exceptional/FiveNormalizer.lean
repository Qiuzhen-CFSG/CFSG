module
public import Theory.GroupAction.FiveSevenCentralizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.ChiefSection
/-!
# Five-subgroup control of the literal section action

A fixed-free group of order five on a section of order 256 has seven-free
centralizer. Its normalizer is seven-free as well, since the automorphism
group of a cyclic group of order five has order four. Frattini's argument
then controls the normalizer of any seven-free inner group in which this
five-subgroup is Sylow. In particular the seven-residual acts trivially on
the section. No abelianity of the section is required.

This is the alternative to the semilinear chief-factor bound in the SL₃(4)
branch of Aschbacher–Smith, 11.1.5, printed p.766. The final theorem uses
the literal O₂(A)/(Z(A) intersect O₂(A)) action from `ChiefSection`; its
SL₃ consumer constructs the five-subgroup and proves every order premise.
-/

open Subgroup
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.ChiefSection

private theorem five_normalizer_seven_coprime
    {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 256)
    (B : Subgroup (MulAut E)) (hB : Nat.card B = 5)
    (hfixed : FixedPoints.subgroup B E = ⊥) :
    Nat.Coprime 7 (Nat.card (normalizer (B : Set (MulAut E)))) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hC := Theory.GroupAction.seven_coprime_centralizer_of_fixed_free_five hE B hB hfixed
  let : IsCyclic B := isCyclic_of_prime_card hB
  have hA : Nat.Coprime 7 (Nat.card (MulAut B)) := by
    rw [IsCyclic.card_mulAut,hB]
    decide
  have hk : Nat.Coprime 7 (Nat.card B.normalizerMonoidHom.ker) := by
    rw [normalizerMonoidHom_ker,
      Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (B : Set (MulAut E)))).toEquiv]
    exact hC
  rw [←B.normalizerMonoidHom.ker.card_mul_index, index_ker]
  exact hk.mul_right (hA.coprime_dvd_right (card_subgroup_dvd_card _))

/-- A normal seven-free inner group with a Sylow subgroup of order five
and a fixed-free action controls its whole normalizer on the section. -/
theorem normalizer_seven_coprime_of_five
    {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 256)
    (H B : Subgroup (MulAut E)) (hBH : B ≤ H)
    (hH : Nat.Coprime 7 (Nat.card H)) (h25 : ¬ 25 ∣ Nat.card H)
    (hB : Nat.card B = 5) (hfixed : FixedPoints.subgroup B E = ⊥) :
    Nat.Coprime 7 (Nat.card (normalizer (H : Set (MulAut E)))) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let N := normalizer (H : Set (MulAut E))
  let J := H.subgroupOf N
  let B' := B.subgroupOf H
  have hb' : Nat.card B' = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv).trans hB
  have hbindex : ¬ 5 ∣ B'.index := by
    intro hd
    apply h25
    have hh := B'.card_mul_index
    rw [hb'] at hh
    rw [←hh]
    exact Nat.mul_dvd_mul_left 5 hd
  let P : Sylow 5 H := (IsPGroup.of_card (p := 5) (n := 1) (by simpa using hb')).toSylow hbindex
  let e := (subgroupOfEquivOfLe H.le_normalizer).symm
  let Q : Sylow 5 J := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let : J.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  have hQ : (Q : Subgroup J).map J.subtype = B.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le (hBH.trans H.le_normalizer)]
    change (((B'.map e.toMonoidHom).map J.subtype).map N.subtype) = B
    rw [map_map,map_map]
    change B'.map H.subtype = B
    exact map_subgroupOf_eq_of_le hBH
  have hfr := Sylow.normalizer_sup_eq_top Q
  rw [hQ] at hfr
  let K := normalizer (B.subgroupOf N : Set N)
  have hKle : K.map N.subtype ≤ normalizer (B : Set (MulAut E)) := by
    rw [←map_subgroupOf_eq_of_le (hBH.trans H.le_normalizer)]
    exact le_normalizer_map _
  have hK : Nat.Coprime 7 (Nat.card K) := by
    have hc := (five_normalizer_seven_coprime hE B hB hfixed).coprime_dvd_right
      (card_dvd_of_le hKle)
    rwa [card_map_of_injective N.subtype_injective] at hc
  have hJ : Nat.Coprime 7 (Nat.card J) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe H.le_normalizer).toEquiv]
    exact hH
  have hi : Nat.Coprime 7 J.index := by
    have he : J.index = J.relIndex K := by
      rw [←relIndex_top_right, ←hfr, relIndex_sup_right]
    rw [he]
    exact hK.coprime_dvd_right (relIndex_dvd_card J K)
  rw [←J.card_mul_index]
  exact hJ.mul_right hi

variable {G : Type*} [Group G] [Finite G] (A : Subgroup G)

omit [Finite G] in
theorem automorphismAction_normalizes_inner (α : MulAut A) :
    automorphismAction A α ∈ normalizer ((innerAction A).range : Set _) := by
  suffices h : (automorphismAction A).range ≤ normalizer ((innerAction A).range : Set _) from
    h ⟨α,rfl⟩
  apply le_normalizer_iff.mpr
  rintro _ ⟨β,rfl⟩ _ ⟨x,rfl⟩
  refine ⟨β x, ?_⟩
  have he : β * MulAut.conj x * β⁻¹ = MulAut.conj (β x) := by
    apply MulEquiv.ext
    intro z
    change β (x * β.symm z * x⁻¹) = β x * z * (β x)⁻¹
    simp only [map_mul,map_inv,MulEquiv.apply_symm_apply]
  have h := congrArg (automorphismAction A) he
  simpa only [map_mul,map_inv,innerAction,MonoidHom.comp_apply] using h.symm

/-- Frattini's argument removes the need to assume the central section
is abelian: the five-action controls the normalizer of the whole inner image. -/
theorem sevenResidual_le_section_kernel_of_five
    {Y : Type*} [Group Y] (a : Y →* MulAut A)
    (hA : Nat.Coprime 7 (Nat.card A)) (h25 : ¬ 25 ∣ Nat.card A)
    (hcard : Nat.card (CoreCentralSection A) = 256)
    (B : Subgroup (MulAut (CoreCentralSection A)))
    (hB : B ≤ (innerAction A).range) (hBcard : Nat.card B = 5)
    (hfixed : FixedPoints.subgroup B (CoreCentralSection A) = ⊥) :
    primeToResidual 7 Y ≤ ((automorphismAction A).comp a).ker := by
  have hH := hA.coprime_dvd_right (card_range_dvd (innerAction A))
  have hH25 : ¬ 25 ∣ Nat.card (innerAction A).range :=
    fun hd => h25 (hd.trans (card_range_dvd (innerAction A)))
  have hN := normalizer_seven_coprime_of_five hcard (innerAction A).range B hB hH hH25 hBcard hfixed
  have hr : ((automorphismAction A).comp a).range ≤
      normalizer ((innerAction A).range : Set _) := by
    rintro _ ⟨y,rfl⟩
    exact automorphismAction_normalizes_inner A (a y)
  apply primeToResidual_le
  rw [index_ker]
  exact hN.coprime_dvd_right (card_dvd_of_le hr)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.ChiefSection
