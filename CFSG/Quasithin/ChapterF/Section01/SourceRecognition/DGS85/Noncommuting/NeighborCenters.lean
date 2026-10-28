module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.DistanceGap
public import Theory.Representation.BinaryConjugationSection.FixedIndex
public import Theory.Representation.BinaryConjugationSection.SharpFixedIndex
public import Theory.SpecificGroups.SL2.ResidualSylowGeneration

/-!
# Splitting the epsilon-two natural center

Distinct Sylows of SL₂ in characteristic two have complementary fixed lines
on its natural binary module. Literal conjugation coordinates identify these
lines with the centers at two distinct neighboring vertices. The exact
edge-Sylow epsilon-two equality and (7.4)(b) remove the central section kernel.
Local transitivity and translation then give the splitting at every vertex
in the critical endpoint orbit.

This is the direct-product assertion used in (7.5)(1), with the actual local
actor, edge two-core and center subgroups. It is consumed by `RadiusTwoControl`
to place the radius-two group in the penultimate even vertex core. It does
not assert the long-distance bound.

Source: DGS, *Groups and Graphs* (1985), (7.5)(1), p.129.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {k : Type*} [Field k] [Finite k] [Algebra (ZMod 2) k]
local notation "N" => SL2NaturalOffenders.NoStrong.natural (F := k)

omit [Finite k] in
private theorem natural_fixed_top : fixedSpace N ⊤ = ⊥ := by
  apply bot_unique
  intro z hz
  have h₀ := congrFun (hz ⟨Matrix.SpecialLinearGroup.transvection
    (i := 0) (j := 1) zero_ne_one (1 : k),mem_top _⟩) 0
  have h₁ := congrFun (hz ⟨Matrix.SpecialLinearGroup.transvection
    (i := 1) (j := 0) one_ne_zero (1 : k),mem_top _⟩) 1
  change (Matrix.SpecialLinearGroup.transvection zero_ne_one (1:k)).val.mulVec z 0 = z 0 at h₀
  change (Matrix.SpecialLinearGroup.transvection one_ne_zero (1:k)).val.mulVec z 1 = z 1 at h₁
  simp [Matrix.SpecialLinearGroup.transvection_coe,Matrix.mulVec,dotProduct,Fin.sum_univ_two] at h₀ h₁
  change z = 0
  ext i
  fin_cases i
  · simpa using h₁
  · simpa using h₀

private theorem natural_sylow_fixed_dim (S : Sylow 2 SL(2,k)) :
    Module.finrank (ZMod 2) (fixedSpace N S) = Module.finrank (ZMod 2) k := by
  let : CharP k 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) k).injective 2
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,k)
    (Matrix.SpecialLinearGroup.upperUnipotentSylow k 2) S
  have hd := (fixedSpaceConjEquiv N
    (Matrix.SpecialLinearGroup.upperUnipotent k) g).finrank_eq
  change Module.finrank (ZMod 2) (fixedSpace N (Matrix.SpecialLinearGroup.upperUnipotent k)) =
    Module.finrank (ZMod 2) (fixedSpace N ((g • Matrix.SpecialLinearGroup.upperUnipotentSylow k 2 :
      Sylow 2 SL(2,k)) : Subgroup SL(2,k))) at hd
  rw [hg] at hd
  exact hd.symm.trans SL2NaturalOffenders.Ratios.upper_fixed_finrank

/-- Distinct natural SL₂ Sylows fix complementary binary subspaces. -/
theorem natural_distinct_sylow_fixed_isCompl (S T : Sylow 2 SL(2,k)) (hne : S ≠ T) :
    IsCompl (fixedSpace N S) (fixedSpace N T) := by
  let : CharP k 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) k).injective 2
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,k) S T
  have hg : g ∉ normalizer (S : Set SL(2,k)) := by
    intro hg
    exact hne (Sylow.smul_eq_iff_mem_normalizer.mpr hg).symm
  have hgen := Matrix.SpecialLinearGroup.sylow_sup_conjugate_eq_top_of_not_mem_normalizer S hg
  have hinf : fixedSpace N S ⊓ fixedSpace N (g • S : Sylow 2 SL(2,k)) = ⊥ := by
    have hf : fixedSpace N ((S : Subgroup SL(2,k)) ⊔
        ((g • S : Sylow 2 SL(2,k)) : Subgroup SL(2,k))) =
        fixedSpace N S ⊓ fixedSpace N (g • S : Sylow 2 SL(2,k)) :=
      (SL2NaturalOffenders.NoStrong.natural (F := k)).invariants_comp_sup _ _
    change (S : Subgroup SL(2,k)) ⊔ ((g • S : Sylow 2 SL(2,k)) : Subgroup SL(2,k)) = ⊤ at hgen
    rw [hgen] at hf
    exact hf.symm.trans natural_fixed_top
  have hdim := (fixedSpace N S).finrank_sup_add_finrank_inf_eq
    (fixedSpace N (g • S : Sylow 2 SL(2,k)))
  rw [hinf,finrank_bot,add_zero,natural_sylow_fixed_dim,natural_sylow_fixed_dim] at hdim
  have hfull : Module.finrank (ZMod 2) (Fin 2 → k) = 2 * Module.finrank (ZMod 2) k := by
    simp [Module.finrank_pi_fintype,two_mul]
  refine ⟨disjoint_iff.mpr hinf,?_⟩
  apply codisjoint_iff.mpr
  exact Submodule.eq_of_le_of_finrank_le le_top (by rw [finrank_top,hfull]; omega)

variable {G : Type*} [Group G]

omit [Finite k] in
private theorem zero_kernel_fixed_image (L Z : Subgroup G) (π : L →* SL(2,k))
    (d : BinaryConjugationSection L Z ⊥ ((N).comp π))
    (S : Subgroup G) (hSL : S ≤ L) :
    d.imageSpace (Z ⊓ centralizer (S : Set G)) = fixedSpace N ((S.subgroupOf L).map π) := by
  have he : commutatorPreimage Z S ⊥ = Z ⊓ centralizer (S : Set G) := by
    apply le_antisymm
    · exact le_inf (commutatorPreimage_le _ _ _)
        (commutator_eq_bot_iff_le_centralizer.mp
          (bot_unique (commutator_commutatorPreimage_le Z S ⊥ le_normalizer_of_normal)))
    · exact le_commutatorPreimage inf_le_left
        (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le
  rw [←fixedSpace_comp_map,←d.fixed_image_eq S hSL le_normalizer_of_normal,he]


private theorem omega_eq_bot_of_center_eq_bot (L : Subgroup G) (hz : center L = ⊥) :
    Stellmacher.omegaOneCenterAmbient L = ⊥ := by
  apply bot_unique
  intro x hx
  obtain ⟨hxL,_,hxc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx
  have hm : (⟨x,hxL⟩ : L) ∈ center L :=
    mem_center_iff.mpr (fun l => Subtype.ext (hxc l l.property))
  rw [hz,mem_bot] at hm
  exact congrArg Subtype.val hm

variable {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The exact epsilon-two edge seed is independent of the chosen neighbor. -/
theorem graph_epsilonTwo_at_neighbor (h : LocallyRankOneTriple P B)
    {v u t : Vertex (family P)} (hvu : (graph (family P)).Adj v u)
    (hvt : (graph (family P)).Adj v t)
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2)) :
    Z (family P) t = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) t).pCoreIn 2) := by
  let := finite_endpoints h
  obtain ⟨g,hg,hgt⟩ := locally_transitive (family P) hvu hvt
  have he := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hepsilon
  rw [←Z_translate,←Stellmacher.omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,
    ←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2 _ (MulAut.conj g).injective,
    map_inf _ _ _ (MulAut.conj g).injective,←stabilizer_translate,←stabilizer_translate,
    show g • v = v from hg,hgt] at he
  exact he

/-- A natural center with trivial local center is the direct product of
the centers at any two distinct epsilon-two neighbors. -/
theorem graph_natural_neighbor_centers_split
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (L : Vertex (family P) → Subgroup G)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    {v u t : Vertex (family P)} (hvu : (graph (family P)).Adj v u)
    (hvt : (graph (family P)).Adj v t) (hut : u ≠ t)
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hcenter : center (L v) = ⊥)
    (hnat : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v)) :
    Z (family P) v = Z (family P) u ⊔ Z (family P) t ∧
      Disjoint (Z (family P) u) (Z (family P) t) := by
  let := finite_endpoints h
  let := graph_Z_elementary h v
  have hLv : L v ≤ stabilizer (family P) v := by rw [←hstar v u hvu]; exact (d v u hvu).Pstar_le
  let : Finite (L v) := Finite.of_injective (inclusion hLv) (inclusion_injective _)
  obtain ⟨k,hk,hfin,halg,π,hπ,_,⟨c⟩⟩ := hnat
  let c₀ : BinaryConjugationSection (L v) (Z (family P) v) ⊥
      (SL2NaturalOffenders.NoStrong.natural.comp π) :=
    omega_eq_bot_of_center_eq_bot (L v) hcenter ▸ c
  have hsyl (x : Vertex (family P)) (hx : (graph (family P)).Adj v x) :
      ∃ S : Sylow 2 (L v), (S : Subgroup (L v)).map (L v).subtype =
        (stabilizer (family P) v ⊓ stabilizer (family P) x).pCoreIn 2 := by
    rw [←hstar v x hx]
    exact ⟨(d v x hx).sylow,local_sylow_eq_edgeCore (d v x hx)
      (by rw [hstar]; exact hodd v) (source_edge_core_sylow h hB hx)⟩
  have heps (x : Vertex (family P)) (hx : (graph (family P)).Adj v x) :=
    graph_epsilonTwo_at_neighbor h hvu hx hepsilon
  have hseed (x : Vertex (family P)) (hx : (graph (family P)).Adj v x) :
      Z (family P) x ≤ Z (family P) v := by
    rw [heps x hx]
    exact graph_edgeSeed_le_Z h hB hx (d v x hx) (by rw [hstar]; exact hodd v)
  obtain ⟨S,hS⟩ := hsyl u hvu
  obtain ⟨T,hT⟩ := hsyl t hvt
  let S' := S.mapSurjective (f := π) hπ
  let T' := T.mapSurjective (f := π) hπ
  have hf (x : Vertex (family P)) (hx : (graph (family P)).Adj v x)
      (A : Sylow 2 (L v)) (hA : (A : Subgroup (L v)).map (L v).subtype =
        (stabilizer (family P) v ⊓ stabilizer (family P) x).pCoreIn 2) :
      c₀.imageSpace (Z (family P) x) = fixedSpace
        SL2NaturalOffenders.NoStrong.natural (A.mapSurjective (f := π) hπ) := by
    let E := (stabilizer (family P) v ⊓ stabilizer (family P) x).pCoreIn 2
    have hEL : E ≤ L v := hA.symm.le.trans (map_subtype_le _)
    have hfixed : Z (family P) v ⊓ centralizer (E : Set G) = Z (family P) x := by
      rw [heps x hx]
      apply elementary_fixed_eq_seed
      · exact ((source_Z_Q_U h v).1.trans (map_subtype_le _)).trans (graph_Q_le_edgeCore h hx)
      · exact graph_edgeSeed_le_Z h hB hx (d v x hx) (by rw [hstar]; exact hodd v)
    rw [←hfixed,zero_kernel_fixed_image (L v) (Z (family P) v) π c₀ E hEL]
    have hae : E.subgroupOf (L v) = A := by
      apply map_injective (L v).subtype_injective
      rw [map_subgroupOf_eq_of_le hEL]
      exact hA.symm
    rw [hae]
    rfl
  have hSf := hf u hvu S hS
  have hTf := hf t hvt T hT
  have hne : S' ≠ T' := by
    intro he
    have himg : c₀.imageSpace (Z (family P) u) = c₀.imageSpace (Z (family P) t) :=
      hSf.trans ((congrArg (fun R : Sylow 2 SL(2,k) =>
        fixedSpace SL2NaturalOffenders.NoStrong.natural (R : Subgroup SL(2,k))) he).trans hTf.symm)
    apply graph_neighbor_centers_ne h hvu hvt hut
    apply le_antisymm
    · intro z hz
      apply (c₀.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le ⟨z,hseed u hvu hz⟩).mp
      rw [←himg]
      exact (c₀.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le _).mpr hz
    · intro z hz
      apply (c₀.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le ⟨z,hseed t hvt hz⟩).mp
      rw [himg]
      exact (c₀.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le _).mpr hz
  have hcompl := natural_distinct_sylow_fixed_isCompl S' T' hne
  refine ⟨c₀.section_eq_sup_of_imageSpace_sup_top _ _ (hseed u hvu) (hseed t hvt) bot_le ?_,?_⟩
  · rw [hSf,hTf]
    exact hcompl.sup_eq_top
  · apply disjoint_iff.mpr
    apply bot_unique
    intro z hz
    have hzu := (c₀.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le ⟨z,hseed u hvu hz.1⟩).mpr hz.1
    have hzt := (c₀.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le ⟨z,hseed u hvu hz.1⟩).mpr hz.2
    rw [hSf] at hzu
    rw [hTf] at hzt
    have hz0 : (c₀.coordinates ⟨z,hseed u hvu hz.1⟩).toAdd ∈ (⊥ : Submodule (ZMod 2) (Fin 2 → k)) := by
      rw [←hcompl.inf_eq_bot]
      exact ⟨hzu,hzt⟩
    exact (c₀.coordinates_eq_one_iff _).mp hz0


/-- Epsilon-two center splitting at every vertex of the critical endpoint type. -/
theorem graph_epsilonTwo_centers_split_of_type
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (L : Vertex (family P) → Subgroup G)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    {v u : Vertex (family P)} (hvu : (graph (family P)).Adj v u)
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    {y a c : Vertex (family P)} (htype : v.type = y.type)
    (hya : (graph (family P)).Adj y a) (hyc : (graph (family P)).Adj y c)
    (hac : a ≠ c) :
    Z (family P) y = Z (family P) a ⊔ Z (family P) c ∧
      Disjoint (Z (family P) a) (Z (family P) c) := by
  let := finite_endpoints h
  have hcenter : center (L v) = ⊥ := by
    rw [←hstar v u hvu]
    exact graph_epsilonTwo_center_trivial_of_localData h hB hvu (d v u hvu) (d u v hvu.symm)
      (by rw [hstar]; exact hodd v) (by rw [hstar]; exact hodd u)
      (by rw [hstar]; exact hdich u) hepsilon
  obtain ⟨g,rfl⟩ := (same_orbit_iff (family P) v y).mpr htype
  have ha : (graph (family P)).Adj v (g⁻¹ • a) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g⁻¹).map_adj_iff.mpr hya
    change (graph (family P)).Adj (g⁻¹ • (g • v)) (g⁻¹ • a) at hh
    simpa only [inv_smul_smul] using hh
  have hc : (graph (family P)).Adj v (g⁻¹ • c) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g⁻¹).map_adj_iff.mpr hyc
    change (graph (family P)).Adj (g⁻¹ • (g • v)) (g⁻¹ • c) at hh
    simpa only [inv_smul_smul] using hh
  have hne : g⁻¹ • a ≠ g⁻¹ • c := fun he => hac ((MulAction.injective g⁻¹) he)
  have heps := graph_epsilonTwo_at_neighbor h hvu ha hepsilon
  obtain ⟨hspan,hdis⟩ := graph_natural_neighbor_centers_split h hB L d hstar hodd
    ha hc hne heps hcenter hnat
  constructor
  · have he := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hspan
    simpa only [Subgroup.map_sup,←Z_translate,smul_inv_smul] using he
  · have he := Subgroup.disjoint_map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective hdis
    simpa only [←Z_translate,smul_inv_smul] using he

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
