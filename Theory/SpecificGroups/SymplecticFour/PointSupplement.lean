module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Lattice
public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.GroupTheory.SylowNormalClosure

/-!
# Point-radical supplements and their marked Sylow subgroups

A subgroup supplementing the elementary point radical is either the whole
point local or has central radical intersection. Its intersection is normal
in the supplement and centralized by the radical, hence normal in the whole
local group; the proved point-radical lattice gives the dichotomy.

In the central case a large endpoint with full upper-root projection has
exactly q² elements and contains the full local center. Every two-subgroup
has order at most q². For the actual pair of marked incident parabolics,
the supplement transports that endpoint into their intersection, so every
Sylow two-subgroup there has exactly q² elements and meets the point radical
in the entire local center. No field-root pair is inferred from its order.

Source: MS93 (5.5), printed pp.916--917. The consumer is
NonbinarySymplectic.CriticalReduction.ContainedPointDichotomy. The further
normalizer/root-pair calculation and individual/paired generation are not
consequences asserted here.
-/

public noncomputable section
open Subgroup Matrix
namespace Theory.SpecificGroups.SymplecticFour.PointSupplement
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- A point-radical supplement is full or meets the radical centrally. -/
theorem supplement_dichotomy {n : ℕ} (hcard : Nat.card F = 2^n) (hn : 1<n)
    (D : Subgroup (pointLocal (F := F))) (hsupp : D ⊔ pointRadical = ⊤) :
    D = ⊤ ∨ D ⊓ pointRadical ≤ center (pointLocal (F := F)) := by
  have hD : D ≤ normalizer (D ⊓ pointRadical : Subgroup (pointLocal (F := F))) :=
    (le_inf D.le_normalizer (le_normalizer_of_normal (H := pointRadical))).trans
      inf_normalizer_le_normalizer_inf
  have hR : pointRadical (F := F) ≤ normalizer (D ⊓ pointRadical : Subgroup (pointLocal (F := F))) := by
    intro r hr
    apply centralizer_le_normalizer ((D ⊓ pointRadical : Subgroup (pointLocal (F := F))) : Set (pointLocal (F := F)))
    intro x hx
    exact pointRadical.le_centralizer hr x hx.2
  let : (D ⊓ pointRadical).Normal := normalizer_eq_top_iff.mp
    (top_le_iff.mp (hsupp ▸ sup_le hD hR))
  rcases PointRadicalAction.normal_radical_dichotomy hcard hn
    (D ⊓ pointRadical) inf_le_right with hc | he
  · exact Or.inr hc
  · left
    have hRD : pointRadical ≤ D := he.symm.le.trans inf_le_left
    simpa only [sup_eq_left.mpr hRD] using hsupp


private theorem center_card {n : ℕ} (hcard : Nat.card F = 2^n) (hn : 1<n) :
    Nat.card (center (pointLocal (F := F))) = Nat.card F := by
  rw [←card_map_of_injective pointLocal.subtype_injective,
    PointRadicalAction.center_eq_root hcard hn,RootSubgroup.card]

private theorem central_kernel_card_bound {n : ℕ} (hcard : Nat.card F = 2^n) (hn : 1<n)
    (D T : Subgroup (pointLocal (F := F)))
    (hc : D ⊓ pointRadical ≤ center (pointLocal (F := F))) (hTD : T ≤ D)
    (hq : Nat.card (T.map pointQuotient) ≤ Nat.card F) : Nat.card T ≤ Nat.card F^2 := by
  have hk : Nat.card (T ⊓ pointQuotient.ker : Subgroup (pointLocal (F := F))) ≤ Nat.card F := by
    rw [←center_card hcard hn]
    exact card_le_of_le ((inf_le_inf_right _ hTD).trans hc)
  rw [←IsElementaryAbelian.card_inf_ker_mul_card_map T pointQuotient,pow_two]
  exact Nat.mul_le_mul hk hq

private theorem rankOne_pgroup_card (T : Subgroup (SpecialLinearGroup (Fin 2) F))
    (hT : IsPGroup 2 T) : Nat.card T ≤ Nat.card F := by
  obtain ⟨S,hS⟩ := hT.exists_le_sylow
  apply (card_le_of_le hS).trans
  have he : Nat.card (S : Subgroup (SpecialLinearGroup (Fin 2) F)) =
      Nat.card ((SpecialLinearGroup.upperUnipotentSylow F 2) : Subgroup (SpecialLinearGroup (Fin 2) F)) := by
    rw [Sylow.card_eq_multiplicity,Sylow.card_eq_multiplicity]
  rw [he]
  exact (SpecialLinearGroup.card_upperUnipotent F).le

/-- Every two-subgroup in the central-intersection branch has order at most q². -/
theorem central_kernel_pgroup_card_bound {n : ℕ} (hcard : Nat.card F = 2^n) (hn : 1<n)
    (D T : Subgroup (pointLocal (F := F)))
    (hc : D ⊓ pointRadical ≤ center (pointLocal (F := F))) (hTD : T ≤ D)
    (hT : IsPGroup 2 T) : Nat.card T ≤ Nat.card F^2 :=
  central_kernel_card_bound hcard hn D T hc hTD
    (rankOne_pgroup_card _ (hT.map pointQuotient))

/-- At the square-order boundary, the radical intersection is the full center. -/
theorem central_kernel_pgroup_at_bound {n : ℕ} (hcard : Nat.card F = 2^n) (hn : 1<n)
    (D T : Subgroup (pointLocal (F := F)))
    (hc : D ⊓ pointRadical ≤ center (pointLocal (F := F))) (hTD : T ≤ D)
    (hT : IsPGroup 2 T) (hsize : Nat.card T = Nat.card F^2) :
    T ⊓ pointRadical = center (pointLocal (F := F)) := by
  apply eq_of_le_of_card_ge ((inf_le_inf_right _ hTD).trans hc)
  rw [center_card hcard hn]
  have he := IsElementaryAbelian.card_inf_ker_mul_card_map T pointQuotient
  rw [pointQuotient_ker,hsize] at he
  have hm := Nat.mul_le_mul_left
    (Nat.card (T ⊓ pointRadical : Subgroup (pointLocal (F := F))))
    (rankOne_pgroup_card _ (hT.map pointQuotient))
  rw [he] at hm
  have hp : 0 < Nat.card F := Nat.card_pos
  nlinarith

/-- A large upper-projecting endpoint fills the upper preimage inside the
supplement, has order q², and meets the radical in the whole center. -/
theorem central_kernel_large_endpoint {n : ℕ} (hcard : Nat.card F = 2^n) (hn : 1<n)
    (D A : Subgroup (pointLocal (F := F)))
    (hc : D ⊓ pointRadical ≤ center (pointLocal (F := F))) (hAD : A ≤ D)
    (hproj : A.map pointQuotient = SpecialLinearGroup.upperUnipotent F)
    (hlarge : Nat.card F^2 ≤ Nat.card A) :
    Nat.card A = Nat.card F^2 ∧
      A ⊓ pointRadical = center (pointLocal (F := F)) ∧
      D ⊓ pointRadical = center (pointLocal (F := F)) ∧
      D ⊓ (SpecialLinearGroup.upperUnipotent F).comap pointQuotient = A := by
  have hsize : Nat.card A = Nat.card F^2 := le_antisymm
    (central_kernel_card_bound hcard hn D A hc hAD
      (by rw [hproj,SpecialLinearGroup.card_upperUnipotent])) hlarge
  have hk : Nat.card (A ⊓ pointRadical : Subgroup (pointLocal (F := F))) = Nat.card F := by
    have he := IsElementaryAbelian.card_inf_ker_mul_card_map A pointQuotient
    rw [pointQuotient_ker,hproj,SpecialLinearGroup.card_upperUnipotent,hsize,pow_two] at he
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos he
  have hAZ : A ⊓ pointRadical = center (pointLocal (F := F)) :=
    eq_of_le_of_card_ge ((inf_le_inf_right _ hAD).trans hc)
      (by rw [hk,center_card hcard hn])
  have hDZ : D ⊓ pointRadical = center (pointLocal (F := F)) :=
    le_antisymm hc (hAZ.symm.le.trans (inf_le_inf_right _ hAD))
  refine ⟨hsize,hAZ,hDZ,?_⟩
  have hAT : A ≤ D ⊓ (SpecialLinearGroup.upperUnipotent F).comap pointQuotient :=
    le_inf hAD (map_le_iff_le_comap.mp hproj.le)
  symm
  apply eq_of_le_of_card_ge hAT
  rw [hsize]
  apply central_kernel_card_bound hcard hn D _ hc inf_le_left
  rw [←SpecialLinearGroup.card_upperUnipotent F]
  exact card_le_of_le (map_le_iff_le_comap.mpr inf_le_right)

omit [CharP F 2] in
private theorem pgroup_le_pointLocal {n : ℕ} (hcard : Nat.card F=2^n) (hn : 1<n)
    (T : Subgroup (Sp F)) (hTP : T ≤ pointParabolic) (hT : IsPGroup 2 T) :
    T ≤ pointLocal := by
  let S : Sylow 2 (pointParabolic (F := F)) := (unipotentSylow hcard (by omega)).subtype
    (unipotent_le_borel.trans inf_le_left)
  have hSN : (S : Subgroup (pointParabolic (F := F))) ≤ pointLocal.subgroupOf pointParabolic :=
    comap_mono (show unipotent ≤ pointLocal (F := F) from inf_le_left)
  have hle := hT.comap_subtype.le_normalClosure_sylow S
  have hle' : T.subgroupOf pointParabolic ≤ pointLocal.subgroupOf pointParabolic :=
    hle.trans (normalClosure_le_normal hSN)
  intro x hx
  exact hle' (show (⟨x,hTP hx⟩ : pointParabolic) ∈ T.subgroupOf pointParabolic from hx)

omit [Finite F] in
private theorem radical_le_plane : (pointRadical (F := F)).map pointLocal.subtype ≤ planeParabolic := by
  rintro _ ⟨x,hx,rfl⟩
  rw [pointRadical_eq_element x hx,mem_planeParabolic_iff]
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- In the central branch, the source Sylow subgroup in the actual two
marked parabolics has exactly q² elements, including the equality boundary. -/
theorem marked_sylow_at_bound {n : ℕ} (hcard : Nat.card F=2^n) (hn : 1<n)
    (J A : Subgroup (Sp F)) (hAJ : A ≤ J) (hAL : A ≤ pointLocal)
    (hAP : A ≤ planeParabolic) (hsize : Nat.card A = Nat.card F^2)
    (hsupp : J.subgroupOf pointLocal ⊔ pointRadical = ⊤)
    (hc : J.subgroupOf pointLocal ⊓ pointRadical ≤ center (pointLocal (F := F)))
    (s w : Sp F) (hs : s∈planeLocal) (hws : w*s∈pointLocal)
    (T : Sylow 2 (J ⊓ planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic : Subgroup (Sp F))) :
    Nat.card T = Nat.card F^2 ∧
      (((T : Subgroup (J ⊓ planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic : Subgroup (Sp F)))).map
        (J ⊓ planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic).subtype).subgroupOf
          pointLocal ⊓ pointRadical = center (pointLocal (F := F)) := by
  let I := J ⊓ planeParabolic.map (MulAut.conj w).toMonoidHom ⊓ pointParabolic
  let D := J.subgroupOf pointLocal
  let z : pointLocal (F := F) := ⟨w*s,hws⟩
  obtain ⟨y,hy,r,hr,hyr⟩ := mem_sup_of_normal_right.mp (hsupp ▸ (mem_top z))
  have hrP : r.val∈planeParabolic := radical_le_plane (mem_map_of_mem pointLocal.subtype hr)
  have hsP := planeLocal_le hs
  let A' := A.map (MulAut.conj y.val).toMonoidHom
  have hA'I : A' ≤ I := by
    rintro x ⟨a,ha,rfl⟩
    refine ⟨⟨J.mul_mem (J.mul_mem hy (hAJ ha)) (J.inv_mem hy),?_⟩,?_⟩
    · refine ⟨s*r.val⁻¹*a*r.val*s⁻¹,?_,?_⟩
      · exact planeParabolic.mul_mem (planeParabolic.mul_mem
          (planeParabolic.mul_mem (planeParabolic.mul_mem hsP (planeParabolic.inv_mem hrP))
            (hAP ha)) hrP) (planeParabolic.inv_mem hsP)
      · have he : y.val*r.val=w*s := congrArg Subtype.val hyr
        have hy' : y.val=w*s*r.val⁻¹ := (eq_mul_inv_iff_mul_eq).mpr he
        change w*(s*r.val⁻¹*a*r.val*s⁻¹)*w⁻¹ = y.val*a*y.val⁻¹
        rw [hy']
        group
    · exact pointLocal_le (pointLocal.mul_mem (pointLocal.mul_mem y.property (hAL ha))
        (pointLocal.inv_mem y.property))
  have hAc : Nat.card A' = Nat.card F^2 := by
    rw [card_map_of_injective (MulAut.conj y.val).injective,hsize]
  have hA2 : IsPGroup 2 A' := IsPGroup.of_card (n := n*2)
    (by rw [hAc,hcard,pow_mul])
  obtain ⟨S,hS⟩ := (show IsPGroup 2 (A'.subgroupOf I) from hA2.comap_subtype).exists_le_sylow
  have hcardS : Nat.card S = Nat.card T := by
    rw [Sylow.card_eq_multiplicity,Sylow.card_eq_multiplicity]
  have hlow : Nat.card F^2 ≤ Nat.card T := by
    rw [←hAc,←map_subgroupOf_eq_of_le hA'I,card_map_of_injective I.subtype_injective]
    exact (card_le_of_le hS).trans_eq hcardS
  let T' := (T : Subgroup I).map I.subtype
  have hT' : T' ≤ pointLocal := pgroup_le_pointLocal hcard hn T'
    ((map_subtype_le _).trans inf_le_right) (T.isPGroup'.map I.subtype)
  have hT'D : T'.subgroupOf pointLocal ≤ D := comap_mono
    ((map_subtype_le _).trans (inf_le_left.trans inf_le_left))
  have hu := central_kernel_pgroup_card_bound hcard hn D (T'.subgroupOf pointLocal)
    hc hT'D (T.isPGroup'.map I.subtype).comap_subtype
  rw [←card_map_of_injective pointLocal.subtype_injective,
    map_subgroupOf_eq_of_le hT',card_map_of_injective I.subtype_injective] at hu
  have hsizeT : Nat.card T = Nat.card F^2 := le_antisymm hu hlow
  refine ⟨hsizeT,?_⟩
  apply central_kernel_pgroup_at_bound hcard hn D (T'.subgroupOf pointLocal)
    hc hT'D (T.isPGroup'.map I.subtype).comap_subtype
  rw [←card_map_of_injective pointLocal.subtype_injective,
    map_subgroupOf_eq_of_le hT',card_map_of_injective I.subtype_injective]
  exact hsizeT
end Theory.SpecificGroups.SymplecticFour.PointSupplement
