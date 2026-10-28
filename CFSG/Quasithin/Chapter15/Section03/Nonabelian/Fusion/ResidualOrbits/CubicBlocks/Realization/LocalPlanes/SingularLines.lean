module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes.SingularLines.Model
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes.Centralizers
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes.Orthogonality

/-!
# Singular commutator lines and the actual local-plane generators

Conjugation through the common actor identifies [Z,D] with the span of the
singular vector z and its complementary cubic image. The span has order four
and lies in the literal determinant hyperplane U ∩ V.

For the generator compatibility, the two actual local-plane generators have
nonzero upper coordinates in different natural summands. Their commutator is
a nonzero pure tensor. Decomposing both elements through U_a V and using the
relative center of the extraspecial U puts this commutator in Z, so it equals
z. Thus the two tensor factors are fixed by the actual ambient elements,
and the pairing formula identifies [⟨a_i⟩,P] with [Z,D(σ i)].

The final theorem uses the literal source subgroups and an actual local-product
equivalence. The layer actions and pairing formula are explicit inputs whose
construction remains with their source owners; no tensor-factor alignment is
assumed. This is the singular-line calculation in the proof of 15.3.61(2),
not the final involution-fusion conclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.53–55
and the first paragraph of 15.3.61(2), printed pp.1146–1147 and 1150.
-/

public section
open Subgroup
open scoped commutatorElement Pointwise
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization

private theorem cyclic_two {G : Type*} [Group G] [Finite G] (x y : G)
    (hx : orderOf x = 2) (hy : y ∈ zpowers x) : y = 1 ∨ y = x := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hx] at hy
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
  have hnlt := Finset.mem_range.mp hn
  interval_cases n <;> simp

variable {G : Type*} [Group G] {I Y P V : Subgroup G}
  {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
  [(V.subgroupOf P).Normal]

/-- The tensor displacement is the actual ambient commutator. -/
theorem tensorEmbedding_displacement (d : LayerActions I Y P V hIP hIV)
    (b : I) (w : TensorVector) :
    tensorEmbedding d (tensorAction (d.actor b) w / w) =
      ⁅(b : G), tensorEmbedding d w⁆ := by
  have he := d.lower_compatible b (d.lowerCoordinates.symm w)
  rw [d.lowerCoordinates.apply_symm_apply] at he
  have hc : tensorEmbedding d (tensorAction (d.actor b) w) =
      (b : G) * tensorEmbedding d w * (b : G)⁻¹ := by
    rw [← he, tensorEmbedding_coordinates]
    rfl
  rw [map_div, hc, div_eq_mul_inv, commutatorElement_def]

/-- The literal source commutator is the cubic tensor line in the supplied
lower coordinates. Only the actual actor image and the generating involution
are needed for this identification. -/
theorem commutator_zpowers_eq_tensorCubicLine [Finite G]
    (d : LayerActions I Y P V hIP hIV) (j : Fin 2) (D : Subgroup G)
    (hDI : D ≤ I) (himage : (D.subgroupOf I).map d.actor = complementaryCubic j)
    (z : V) (hz : z ≠ 1) :
    ⁅zpowers (z : G), D⁆ = (tensorCubicLine j (d.lowerCoordinates z)).map (tensorEmbedding d) := by
  have hz2 : orderOf (z : G) = 2 := by
    let := d.elementary_lower
    apply orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (z : G) z.property)
    intro h
    exact hz (Subtype.ext h)
  rw [commutator_comm]
  apply le_antisymm
  · apply commutator_le.mpr
    intro b hb x hx
    rcases cyclic_two (z : G) x hz2 hx with rfl | rfl
    · simp
    · have ha : d.actor ⟨b, hDI hb⟩ ∈ complementaryCubic j := by
        rw [← himage]
        exact mem_map_of_mem _ hb
      have h := mem_map_of_mem (tensorEmbedding d)
        (SingularLineModel.displacement_mem j (d.lowerCoordinates z) _ ha)
      rwa [tensorEmbedding_displacement, tensorEmbedding_coordinates] at h
  · have hd (n : ℕ) : tensorEmbedding d
        (tensorAction (complementaryRotation j ^ n) (d.lowerCoordinates z) /
          d.lowerCoordinates z) ∈ ⁅D, zpowers (z : G)⁆ := by
      have hm : complementaryRotation j ^ n ∈ (D.subgroupOf I).map d.actor := by
        rw [himage]
        exact (complementaryCubic j).pow_mem (mem_zpowers _) n
      obtain ⟨b, hb, he⟩ := hm
      rw [← he, tensorEmbedding_displacement, tensorEmbedding_coordinates]
      exact commutator_mem_commutator hb (mem_zpowers _)
    have h1 : tensorEmbedding d (tensorAction (complementaryRotation j)
        (d.lowerCoordinates z) / d.lowerCoordinates z) ∈ ⁅D, zpowers (z : G)⁆ := by
      simpa using hd 1
    have hzmem : tensorEmbedding d (d.lowerCoordinates z) ∈ ⁅D, zpowers (z : G)⁆ := by
      rw [SingularLineModel.displacement_recover j (d.lowerCoordinates z), map_mul]
      exact mul_mem h1 (hd 2)
    have hrmem : tensorEmbedding d (tensorAction (complementaryRotation j)
        (d.lowerCoordinates z)) ∈ ⁅D, zpowers (z : G)⁆ := by
      rw [SingularLineModel.rotation_recover j (d.lowerCoordinates z), map_mul]
      exact mul_mem hzmem h1
    rw [tensorCubicLine, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le (zpowers_le.mpr hzmem) (zpowers_le.mpr hrmem)

/-- The source singular line has order four, is contained in the specified
intersection, and every one of its elements has determinant zero. -/
theorem singular_commutator_properties [Finite G]
    (d : LayerActions I Y P V hIP hIV) (U Z : Subgroup G)
    (j : Fin 2) (D : Subgroup G) (hDI : D ≤ I)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic j)
    (z : V) (hz : z ≠ 1) (hZ : zpowers (z : G) = Z)
    (hsing : (d.lowerCoordinates z).toAdd.det = 0)
    (hUV : U ⊓ V = sourceHyperplane d z) :
    ⁅Z, D⁆ = (tensorCubicLine j (d.lowerCoordinates z)).map (tensorEmbedding d) ∧
    Nat.card (⁅Z, D⁆ : Subgroup G) = 4 ∧ ⁅Z, D⁆ ≤ U ⊓ V ∧
    ∀ v : V, (v : G) ∈ ⁅Z, D⁆ → (d.lowerCoordinates v).toAdd.det = 0 := by
  have he := commutator_zpowers_eq_tensorCubicLine d j D hDI himage z hz
  rw [hZ] at he
  refine ⟨he, ?_, ?_, ?_⟩
  · rw [he, card_map_of_injective (tensorEmbedding_injective d)]
    exact SingularLineModel.line_card j _ (fun h => hz (d.lowerCoordinates.injective
      (h.trans (map_one d.lowerCoordinates).symm)))
  · rw [hUV, he]
    exact map_mono (SingularLineModel.line_le_hyperplane j _ hsing)
  · intro v hv
    rw [he] at hv
    obtain ⟨w, hw, hew⟩ := hv
    have hew' : w = d.lowerCoordinates v := tensorEmbedding_injective d
      (hew.trans (tensorEmbedding_coordinates d v).symm)
    rw [← hew']
    exact SingularLineModel.line_singular j _ hsing w hw


private theorem upperMap_eq_one_iff (d : LayerActions I Y P V hIP hIV) (x : P) :
    upperMap d x = 1 ↔ (x : G) ∈ V := by
  change d.upperCoordinates (QuotientGroup.mk' _ x) = 1 ↔ _
  rw [← map_one d.upperCoordinates, d.upperCoordinates.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

private theorem upperMap_surjective (d : LayerActions I Y P V hIP hIV) :
    Function.Surjective (upperMap d) :=
  d.upperCoordinates.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The pairing formula evaluated in the ambient group. -/
theorem commutator_eq_tensorEmbedding (d : LayerActions I Y P V hIP hIV)
    (hf : PairingFormula d) (x y : P) :
    ⁅(x : G), (y : G)⁆ = tensorEmbedding d
      (SingularLineModel.pairingVector (upperMap d x) (upperMap d y)) := by
  obtain ⟨hm, he⟩ := hf.commutator x y
  change d.lowerCoordinates _ = SingularLineModel.pairingVector _ _ at he
  rw [← he, tensorEmbedding_coordinates]
  rfl

/-- The entire commutator subgroup of an involution with a pure upper
coordinate is the tensor image obtained by varying the other factor. -/
theorem pure_generator_commutator [Finite G]
    (d : LayerActions I Y P V hIP hIV) (hf : PairingFormula d)
    (j : Fin 2) (x : P) (hx2 : orderOf (x : G) = 2) (u : Plane)
    (hxu : upperMap d x = SingularLineModel.pureUpper j u) :
    ⁅zpowers (x : G), P⁆ =
      (SingularLineModel.pairMap j u).range.map (tensorEmbedding d) := by
  apply le_antisymm
  · apply commutator_le.mpr
    intro b hb y hy
    rcases cyclic_two (x : G) b hx2 hb with rfl | rfl
    · simp
    · rw [commutator_eq_tensorEmbedding d hf x ⟨y, hy⟩, hxu,
        SingularLineModel.pairing_pure]
      exact mem_map_of_mem _ ⟨_, rfl⟩
  · rintro _ ⟨w, ⟨v, rfl⟩, rfl⟩
    obtain ⟨y, hy⟩ := upperMap_surjective d (SingularLineModel.pureUpper (j + 1) v)
    have h := commutator_mem_commutator (mem_zpowers (x : G)) y.property
    have hj : j ≠ j + 1 := by fin_cases j <;> decide
    rw [commutator_eq_tensorEmbedding d hf x y, hxu, hy,
      SingularLineModel.pairing_cross j (j + 1) u v hj] at h
    exact h

omit [(V.subgroupOf P).Normal] in
private theorem central_lower (hcenter : V = (center P).map P.subtype) :
    V ≤ centralizer (P : Set G) := by
  rw [hcenter]
  rintro v ⟨vP, hc, rfl⟩
  intro x hx
  exact congrArg Subtype.val (mem_center_iff.mp hc ⟨x, hx⟩)

omit [(V.subgroupOf P).Normal] in
/-- Adjoining a central subgroup does not change the commutators coming
from an extraspecial subgroup. All centers here are relative centers. -/
theorem local_join_commutator_mem_center
    (U Ua Z : Subgroup G) [IsExtraspecial 2 U]
    (hUa : Ua ≤ U) (hLP : Ua ⊔ V ≤ P)
    (hcentral : V ≤ centralizer (P : Set G))
    (hUZ : (center U).map U.subtype = Z)
    (x y : G) (hx : x ∈ Ua ⊔ V) (hy : y ∈ Ua ⊔ V) : ⁅x, y⁆ ∈ Z := by
  have hprod : ((Ua ⊔ V : Subgroup G) : Set G) = (Ua : Set G) * (V : Set G) :=
    coe_mul_of_right_le_normalizer_left Ua V
      ((hcentral.trans (centralizer_le (show (Ua : Set G) ⊆ P from fun _ hx => hLP (mem_sup_left hx)))).trans
        (Subgroup.centralizer_le_normalizer _))
  change x ∈ ((Ua ⊔ V : Subgroup G) : Set G) at hx
  change y ∈ ((Ua ⊔ V : Subgroup G) : Set G) at hy
  rw [hprod] at hx hy
  obtain ⟨u, hu, v, hv, rfl⟩ := hx
  obtain ⟨r, hr, s, hs, rfl⟩ := hy
  have hvy : Commute v (r * s) :=
    (show Commute (r * s) v from mem_centralizer_iff.mp (hcentral hv) (r * s)
      (P.mul_mem (hLP (mem_sup_left hr)) (hLP (mem_sup_right hs)))).symm
  have hus : Commute u s := mem_centralizer_iff.mp (hcentral hs) u (hLP (mem_sup_left hu))
  rw [commutatorElement_mul_left_eq_conj_mul,
    commutatorElement_eq_one_iff_commute.mpr hvy]
  simp only [mul_one, mul_inv_cancel, one_mul]
  rw [commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_eq_one_iff_commute.mpr hus]
  simp only [mul_one, mul_inv_cancel_right]
  have hc : ⁅(⟨u, hUa hu⟩ : U), (⟨r, hUa hr⟩ : U)⁆ ∈ center U := by
    let := (IsExtraspecial.quotient_elementary_abelian 2 U).toIsMulCommutative
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (center U) _ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  rw [← hUZ]
  exact mem_map_of_mem U.subtype hc

/-- Actual generators in the two aligned planes have cross-commutator z.
This fixes the pure tensor factors, without assuming any coordinate marking
for the chosen local-product equivalence. -/
theorem aligned_generators_cross_commutator [Finite G]
    (d : LayerActions I Y P V hIP hIV) (hf : PairingFormula d)
    (U Ua Z : Subgroup G) [IsExtraspecial 2 U]
    (hUa : Ua ≤ U) (hLP : Ua ⊔ V ≤ P)
    (hcentral : V ≤ centralizer (P : Set G))
    (hUZ : (center U).map U.subtype = Z)
    (z : V) (hz : z ≠ 1) (hZ : zpowers (z : G) = Z)
    (j k : Fin 2) (hjk : j ≠ k)
    (x y : P) (hxL : (x : G) ∈ Ua ⊔ V) (hyL : (y : G) ∈ Ua ⊔ V)
    (hxV : (x : G) ∉ V) (hyV : (y : G) ∉ V)
    (hxj : upperMap d x ∈ naturalSummand j) (hyk : upperMap d y ∈ naturalSummand k) :
    ⁅(x : G), (y : G)⁆ = (z : G) := by
  obtain ⟨u, hu⟩ := SingularLineModel.exists_pureUpper j _ hxj
  obtain ⟨v, hv⟩ := SingularLineModel.exists_pureUpper k _ hyk
  have hu1 : u ≠ 1 := by
    intro h
    apply hxV
    apply (upperMap_eq_one_iff d x).mp
    rw [hu]
    exact (SingularLineModel.pureUpper_ne_one j u).mpr h
  have hv1 : v ≠ 1 := by
    intro h
    apply hyV
    apply (upperMap_eq_one_iff d y).mp
    rw [hv]
    exact (SingularLineModel.pureUpper_ne_one k v).mpr h
  have hne : ⁅(x : G), (y : G)⁆ ≠ 1 := by
    rw [commutator_eq_tensorEmbedding d hf, hu, hv,
      SingularLineModel.pairing_cross j k u v hjk]
    intro h
    exact SingularLineModel.purePair_ne_one j u v hu1 hv1
      (tensorEmbedding_injective d (h.trans (map_one (tensorEmbedding d)).symm))
  have hm := local_join_commutator_mem_center U Ua Z hUa hLP hcentral hUZ
    (x : G) (y : G) hxL hyL
  rw [← hZ] at hm
  have hz2 : orderOf (z : G) = 2 := by
    let := d.elementary_lower
    apply orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (z : G) z.property)
    intro h
    exact hz (Subtype.ext h)
  exact (cyclic_two (z : G) _ hz2 hm).resolve_left hne

/-- The tensor factors determined by the cross-commutator identify the full
commutator image of either aligned generator. -/
theorem aligned_generator_commutator_line [Finite G]
    (d : LayerActions I Y P V hIP hIV) (hf : PairingFormula d)
    (U Ua Z : Subgroup G) [IsExtraspecial 2 U]
    (hUa : Ua ≤ U) (hLP : Ua ⊔ V ≤ P)
    (hcentral : V ≤ centralizer (P : Set G))
    (hUZ : (center U).map U.subtype = Z)
    (z : V) (hz : z ≠ 1) (hZ : zpowers (z : G) = Z)
    (j k : Fin 2) (hjk : j ≠ k)
    (x y : P) (hxL : (x : G) ∈ Ua ⊔ V) (hyL : (y : G) ∈ Ua ⊔ V)
    (hxV : (x : G) ∉ V) (hyV : (y : G) ∉ V) (hx2 : orderOf (x : G) = 2)
    (hxj : upperMap d x ∈ naturalSummand j) (hyk : upperMap d y ∈ naturalSummand k) :
    ⁅zpowers (x : G), P⁆ =
      (tensorCubicLine j (d.lowerCoordinates z)).map (tensorEmbedding d) := by
  obtain ⟨u, hu⟩ := SingularLineModel.exists_pureUpper j _ hxj
  obtain ⟨v, hv⟩ := SingularLineModel.exists_pureUpper k _ hyk
  have hv1 : v ≠ 1 := by
    intro h
    apply hyV
    apply (upperMap_eq_one_iff d y).mp
    rw [hv]
    exact (SingularLineModel.pureUpper_ne_one k v).mpr h
  have he := aligned_generators_cross_commutator d hf U Ua Z hUa hLP hcentral hUZ
    z hz hZ j k hjk x y hxL hyL hxV hyV hxj hyk
  rw [commutator_eq_tensorEmbedding d hf, hu, hv,
    SingularLineModel.pairing_cross j k u v hjk] at he
  have hzcoord : d.lowerCoordinates z = SingularLineModel.purePair j u v :=
    (tensorEmbedding_injective d (he.trans (tensorEmbedding_coordinates d z).symm)).symm
  rw [hzcoord, SingularLineModel.line_eq_pairRange j u v hv1]
  exact pure_generator_commutator d hf j x hx2 u hu


/-- The singular commutator lines and their compatibility with every family
of actual local-plane generators supplied by `exists_localPlane_cubic_data`.
The coordinate marking is derived from the cross-plane commutator. No
identification of a chosen generator with a tensor factor is an input.

The order of U, normalization of U by V, the cardinality of D, and the
remaining generator specifications are unnecessary once these displayed
source inputs and the proved plane alignment are available. -/
theorem localPlane_singular_commutator_lines [Finite G]
    (Z ZS Y V : Subgroup G) (g : G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [(V.subgroupOf (pairP Z ZS g)).Normal]
    [IsExtraspecial 2 (closureU Z ZS)]
    {hIP : pairI Z ZS g ≤ normalizer (pairP Z ZS g : Set G)}
    {hIV : pairI Z ZS g ≤ normalizer (V : Set G)}
    (d : LayerActions (pairI Z ZS g) Y (pairP Z ZS g) V hIP hIV)
    (hf : PairingFormula d) (a : centralizerH Z)
    (e : (fixedLift Z ZS a ⊔ V : Subgroup G) ≃* CentralProductModel)
    (hLP : fixedLift Z ZS a ⊔ V ≤ pairP Z ZS g)
    (hcenter : V = (center (pairP Z ZS g)).map (pairP Z ZS g).subtype)
    (hUZ : (center (closureU Z ZS)).map (closureU Z ZS).subtype = Z)
    (hUa : fixedLift Z ZS a = closureU Z ZS ⊓ centralizer (V : Set G))
    (z : V) (hz : z ≠ 1) (hZ : zpowers (z : G) = Z)
    (hsing : (d.lowerCoordinates z).toAdd.det = 0)
    (hUV : closureU Z ZS ⊓ V = sourceHyperplane d z)
    (D : Fin 2 → Subgroup G) (hDI : ∀ j, D j ≤ pairI Z ZS g)
    (himage : ∀ j, ((D j).subgroupOf (pairI Z ZS g)).map d.actor = complementaryCubic j)
    (σ : Equiv.Perm (Fin 2)) (ai : Fin 2 → G)
    (hplanes : ∀ i, localPlane (fixedLift Z ZS a ⊔ V) e i ≤ summandPreimage d (σ i))
    (hai : ∀ i, ai i ∈ localPlane (fixedLift Z ZS a ⊔ V) e i ⊓
      centralizer (D (σ i) : Set G))
    (hai2 : ∀ i, orderOf (ai i) = 2) (haiV : ∀ i, ai i ∉ V) :
    (∀ j, ⁅Z, D j⁆ = (tensorCubicLine j (d.lowerCoordinates z)).map (tensorEmbedding d) ∧
      Nat.card (⁅Z, D j⁆ : Subgroup G) = 4 ∧ ⁅Z, D j⁆ ≤ closureU Z ZS ⊓ V ∧
      ∀ v : V, (v : G) ∈ ⁅Z, D j⁆ → (d.lowerCoordinates v).toAdd.det = 0) ∧
    (∀ i, ⁅zpowers (ai i), pairP Z ZS g⁆ = ⁅Z, D (σ i)⁆) := by
  have hlines (j : Fin 2) := singular_commutator_properties d (closureU Z ZS) Z
    j (D j) (hDI j) (himage j) z hz hZ hsing hUV
  refine ⟨hlines, fun i => ?_⟩
  have haiL (k : Fin 2) : ai k ∈ fixedLift Z ZS a ⊔ V :=
    localPlane_le _ e k (hai k).1
  let x : pairP Z ZS g := ⟨ai i, hLP (haiL i)⟩
  let y : pairP Z ZS g := ⟨ai (i + 1), hLP (haiL (i + 1))⟩
  have hne : σ i ≠ σ (i + 1) := by
    intro h
    have hh := σ.injective h
    fin_cases i <;> simp at hh
  have he := aligned_generator_commutator_line d hf (closureU Z ZS) (fixedLift Z ZS a) Z
    (by rw [hUa]; exact inf_le_left) hLP (central_lower hcenter) hUZ z hz hZ (σ i) (σ (i + 1)) hne
    x y (haiL i) (haiL (i + 1)) (haiV i) (haiV (i + 1)) (hai2 i)
    ((mem_summandPreimage d (σ i) x).mp (hplanes i (hai i).1))
    ((mem_summandPreimage d (σ (i + 1)) y).mp (hplanes (i + 1) (hai (i + 1)).1))
  exact he.trans (hlines (σ i)).1.symm

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
