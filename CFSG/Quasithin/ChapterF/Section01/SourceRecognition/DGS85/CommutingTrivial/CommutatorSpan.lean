module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.RadiusTwo
public import Theory.SpecificGroups.SL2.FiveGeneratorRecognition

/-!
# Whole-span reduction and exact center orders in Chapter 9

Let R = [V_beta,V_alpha-prime], and let x be the second vertex after alpha
on the actual critical geodesic. The full quotient index makes the opposite
span map onto a Sylow of L_beta/Q_beta. An element g of L_beta exchanges x
and alpha. The two distinct quotient Sylows generate, so normalization and
local conjugate generation give V_beta = R R^g Z_x. All these factors lie
in the elementary abelian V_beta; their subgroup joins are their products.

The actual natural alpha action gives |Z_alpha| = q^2 and |Z_beta| = q.
Consequently, once the geometric containment R <= Z_x is proved, the span
identity gives V_beta = Z_alpha Z_x. The original centralizer index and
these center orders give |V_beta| = q^3 and C_{V_beta}(V_alpha-prime) = Z_x.
The final F1.11 application constructs the markings and natural sections
before using these arguments. It retains the genuine earlier catalogue,
Chapter 8, and 6.5 premises. The geometric containment, the other endpoint
commutator bound, and the terminal distance and field conclusions remain
with the Chapter 9 proof; they are not asserted by this reduction.

Source: DGS, Groups and Graphs (1985), 9.8, printed pp.145--146,
using the natural-module properties on p.113 and 9.3--9.4 on pp.142--143.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Two conjugate full-index two-actors fixing different neighbors generate
the actual local group modulo its actual two-core. -/
theorem linear_local_full_index_conjugate_generation
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v x : Vertex (family P)} (hx : (graph (family P)).Adj v x)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (A : Subgroup G) (hAH : A ≤ graphLocalGroup (family P) v) (hpA : IsPGroup 2 A)
    (hi : (Q (family P) v).relIndex A = Nat.card F)
    (hAx : A ≤ stabilizer (family P) x)
    (g : graphLocalGroup (family P) v) (hg : (g : G) • x ≠ x) :
    graphLocalGroup (family P) v = Q (family P) v ⊔ A ⊔ A.map (MulAut.conj (g : G)).toMonoidHom := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let J := Q Γ v ⊔ A ⊔ A.map (MulAut.conj (g : G)).toMonoidHom
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkmap : q.ker.map H.subtype = Q Γ v := hk ▸ graphLocalGroup_core h v
  let I := (A.subgroupOf H).map q
  have hpI : IsPGroup 2 I := hpA.comap_subtype.map q
  have hcI : Nat.card I = Nat.card F := by
    rw [←relIndex_ker,←relIndex_map_map_of_injective _ _ H.subtype_injective,
      hkmap,map_subgroupOf_eq_of_le hAH,hi]
  obtain ⟨T,hT⟩ := local_quotient_neighbor_stabilizer h hB hS hx e
  change ∀ l : H, q l ∈ normalizer (T : Set SL(2,F)) ↔ (l : G) • x = x at hT
  have hIN : I ≤ normalizer (T : Set SL(2,F)) := by
    rintro _ ⟨a,ha,rfl⟩
    exact (hT a).mpr (hAx ha)
  have hIT : I ≤ T := by
    have hh := hpI.inf_normalizer_sylow T
    rw [inf_eq_left.mpr hIN] at hh
    exact hh.le.trans inf_le_right
  have he : I = T := eq_of_le_of_card_ge hIT (by
    rw [hcI]
    exact (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).toEquiv).ge)
  let T' := T.mapSurjective (f := (MulAut.conj (q g)).toMonoidHom) (MulAut.conj (q g)).surjective
  have hne : T ≠ T' := by
    intro hh
    have hm : (T : Subgroup SL(2,F)).map (MulAut.conj (q g)).toMonoidHom = T :=
      congrArg Sylow.toSubgroup hh.symm
    exact hg ((hT g).mp (mem_normalizer_iff_map_conj_eq.mpr hm))
  have hTJ : (T : Subgroup SL(2,F)) ≤ (J.subgroupOf H).map q := by
    rw [←he]
    exact map_mono (comap_mono (show A ≤ J from le_sup_right.trans le_sup_left))
  have hT'J : (T' : Subgroup SL(2,F)) ≤ (J.subgroupOf H).map q := by
    rintro _ ⟨t,ht,rfl⟩
    obtain ⟨a,ha,rfl⟩ := he.symm ▸ ht
    refine ⟨g*a*g⁻¹,?_,?_⟩
    · exact (show A.map (MulAut.conj (g : G)).toMonoidHom ≤ J from le_sup_right)
        (mem_map_of_mem (MulAut.conj (g : G)).toMonoidHom ha)
    · change q (g*a*g⁻¹) = q g * q a * (q g)⁻¹
      simp only [map_mul,map_inv]
  have hJmap : (J.subgroupOf H).map q = ⊤ := top_unique (by
    rw [←Matrix.SpecialLinearGroup.sylow_sup_eq_top 2 T T' hne]
    exact sup_le hTJ hT'J)
  have hkJ : q.ker ≤ J.subgroupOf H := by
    intro a ha
    exact (show Q Γ v ≤ J from le_sup_left.trans le_sup_left)
      (hkmap ▸ mem_map_of_mem H.subtype ha)
  have hJtop : J.subgroupOf H = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hJmap
    simpa only [comap_map_eq_self hkJ,comap_top] using hh
  apply le_antisymm
  · intro a ha
    exact (show (⟨a,ha⟩ : H) ∈ J.subgroupOf H by rw [hJtop]; trivial)
  · refine sup_le (sup_le (core_le_graphLocalGroup h v) hAH) ?_
    rintro _ ⟨a,ha,rfl⟩
    exact H.mul_mem (H.mul_mem g.property (hAH ha)) (H.inv_mem g.property)

/-- The two opposite Sylow displacements and one neighboring center generate
all of the original neighborhood span. -/
theorem linear_neighborhood_commutator_span
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v x : Vertex (family P)} (hx : (graph (family P)).Adj v x)
    (hz : Z (family P) v ≤ Z (family P) x)
    (hcore : ⁅Q (family P) v,V (family P) v 1⁆ ≤ Z (family P) v)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F))
    (A : Subgroup G) (hAH : A ≤ graphLocalGroup (family P) v) (hpA : IsPGroup 2 A)
    (hi : (Q (family P) v).relIndex A = Nat.card F)
    (hAx : A ≤ stabilizer (family P) x)
    (g : graphLocalGroup (family P) v) (hg : (g : G) • x ≠ x) :
    V (family P) v 1 = ⁅V (family P) v 1,A⁆ ⊔
      (⁅V (family P) v 1,A⁆ : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom ⊔
      Z (family P) x := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ v
  let D := V Γ v 1
  let R := ⁅D,A⁆
  let f := (MulAut.conj (g : G)).toMonoidHom
  let W := R ⊔ R.map f ⊔ Z Γ x
  have hHN : H ≤ normalizer (D : Set G) := (sylowGenerated_le _).trans (stabilizer_normalizes_V Γ v 1)
  have hDm : D.map f = D := mem_normalizer_iff_map_conj_eq.mp (hHN g.property)
  have hRD : R ≤ D := le_normalizer_iff_commutator_le_left.mp (hAH.trans hHN)
  have hWD : W ≤ D := sup_le (sup_le hRD ((map_mono hRD).trans_eq hDm))
    (CommutingNontrivial.Z_neighbor_le_V Γ hx)
  have hconj : ⁅D,A.map f⁆ = R.map f := by rw [map_commutator,hDm]
  have hHW : H ≤ normalizer (W : Set G) := by
    change graphLocalGroup (family P) v ≤ normalizer (W : Set G)
    rw [linear_local_full_index_conjugate_generation h hB hS hx e A hAH hpA hi hAx g hg]
    apply sup_le (sup_le ?_ ?_) ?_
    · apply le_normalizer_iff_commutator_le_right.mpr
      exact (commutator_mono le_rfl hWD).trans (hcore.trans (hz.trans le_sup_right))
    · apply le_normalizer_iff_commutator_le_left.mpr
      exact (commutator_mono hWD le_rfl).trans (le_sup_left.trans le_sup_left)
    · apply le_normalizer_iff_commutator_le_left.mpr
      exact (commutator_mono hWD le_rfl).trans (hconj.le.trans (le_sup_right.trans le_sup_left))
  have hspan := CommutingThreeProfile.V_eq_center_sup_neighbor_conjugates Γ H
    (sylowGenerated_le _) hx
    (fun z hz' => graphLocalGroup_transitive h hB hS v ⟨x,hx⟩ ⟨z,hz'⟩)
  exact le_antisymm (hspan.le.trans (sup_le (hz.trans le_sup_right)
    (conjugateSpanBy_le le_sup_right hHW))) hWD

universe u
variable {G₀ : Type u} [Group G₀] {L : Fin 2 → Subgroup G₀} {S₀ : Subgroup G₀}

/-- The opening reduction of 9.8 on the actual critical path. The original
opposite span and its conjugate supply the two displacement factors. -/
theorem reduced_linear_commutator_span
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (eβ : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F))
    (hi : (Q (Reduction.reducedFamily L S₀) beta).relIndex
      (V (Reduction.reducedFamily L S₀) a' 1) = Nat.card F)
    (hcore : ⁅Q (Reduction.reducedFamily L S₀) beta,V (Reduction.reducedFamily L S₀) beta 1⁆ =
      Z (Reduction.reducedFamily L S₀) beta) :
    let Γ := Reduction.reducedFamily L S₀
    let R := ⁅V Γ beta 1,V Γ a' 1⁆
    ∃ x : Vertex Γ, (graph Γ).Adj beta x ∧ (graph Γ).dist x a' + 2 = b Γ ∧
      ∃ g : graphLocalGroup Γ beta, (g : Reduction.G₀ L S₀) • x = a ∧
        V Γ beta 1 = R ⊔ R.map (MulAut.conj (g : Reduction.G₀ L S₀)).toMonoidHom ⊔ Z Γ x ∧
        (R ≤ Z Γ x → V Γ beta 1 = Z Γ a ⊔ Z Γ x) := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  have hZ := fun z => (source_Z_Q_U ht z).1
  have hSyl := Reduction.reduced_kernel_sylow h
  obtain ⟨_,hb3,hω,_⟩ := Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm
  have hb2 : 2 < b Γ := by change 3 ≤ b Γ at hb3; omega
  change (graph Γ).dist beta a' + 1 = b Γ at hd
  have hcd : (graph Γ).dist a a' = b Γ := hc.1
  have hne : a' ≠ beta := by
    intro he
    have hh := hd
    rw [he,SimpleGraph.dist_self] at hh
    omega
  obtain ⟨x,hx,hxd⟩ := exists_predecessor Γ ht.generate a' beta hne
  have hdx : (graph Γ).dist x a' + 2 = b Γ := by
    rw [SimpleGraph.dist_comm (u := x) (v := a')]
    rw [SimpleGraph.dist_comm (u := a') (v := beta)] at hxd
    omega
  have hax : a ≠ x := by
    intro he
    rw [←he,hcd] at hdx
    omega
  obtain ⟨g,hgx,_,_⟩ := linear_local_neighbor_exchange ht hB hS hx hab.symm eβ
  change graphLocalGroup Γ beta at g
  change (g : Reduction.G₀ L S₀) • x = a at hgx
  have hgm : (g : Reduction.G₀ L S₀) • x ≠ x := by rw [hgx]; exact hax
  have hAH : V Γ a' 1 ≤ graphLocalGroup Γ beta := neighbor_le_graphLocalGroup ht hSyl a' beta hb
    (by change (graph Γ).dist a' beta + 1 ≤ b Γ
        rw [SimpleGraph.dist_comm]; exact hd.le)
  have hpA : IsPGroup 2 (V Γ a' 1) := (isPGroup_pCoreIn 2 (stabilizer Γ a')).to_le
    (V_le_Q Γ ht.generate hZ hSyl a' (r := 1) hb)
  have hAx : V Γ a' 1 ≤ stabilizer Γ x := V_le_stabilizer Γ ht.generate a' x
    (by rw [SimpleGraph.dist_comm]; omega)
  have hz : Z Γ beta ≤ Z Γ x := hω ▸ intrinsic_local_omega_le_neighbor_Z ht hB hS hx
  have hspan := linear_neighborhood_commutator_span ht hB hS hx hz hcore.le eβ _ hAH hpA hi hAx g hgm
  change V Γ beta 1 = ⁅V Γ beta 1,V Γ a' 1⁆ ⊔
    (⁅V Γ beta 1,V Γ a' 1⁆ : Subgroup (Reduction.G₀ L S₀)).map
      (MulAut.conj (g : Reduction.G₀ L S₀)).toMonoidHom ⊔ Z Γ x at hspan
  refine ⟨x,hx,hdx,g,hgx,hspan,?_⟩
  intro hR
  apply le_antisymm ?_ (sup_le (CommutingNontrivial.Z_neighbor_le_V Γ hab.symm)
    (CommutingNontrivial.Z_neighbor_le_V Γ hx))
  rw [hspan]
  apply sup_le (sup_le (hR.trans le_sup_right) ?_) le_sup_right
  have hm := map_mono (f := (MulAut.conj (g : Reduction.G₀ L S₀)).toMonoidHom) hR
  rw [←Z_translate,hgx] at hm
  exact hm.trans le_sup_left

/-- A natural neighboring center has order q² and its beta omega-center
has order q, on the same literal conjugation action. -/
theorem linear_natural_neighbor_center_orders
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hvw : (graph (family P)).Adj v w)
    (hne : ¬ Q (family P) w ≤ Q (family P) v)
    (hz : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F)) :
    letI := Z_elementary (family P) (fun x => (source_Z_Q_U h x).1) v
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) v)))
    ∀ ρ : Representation (ZMod 2) SL(2,F) (Additive (Z (family P) v)),
      (∀ (l : graphLocalGroup (family P) v) (z : Additive (Z (family P) v)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      Function.Injective ρ → (∃ S : Sylow 2 SL(2,F), IsSourceNatural ρ S n) →
      Nat.card (Z (family P) v) = Nat.card F ^ 2 ∧ Nat.card (Z (family P) w) = Nat.card F := by
  let := finite_endpoints h
  let := Z_elementary (family P) (fun x => (source_Z_Q_U h x).1) v
  let : Finite (Z (family P) v) := Finite.of_injective
    (inclusion (Z_le_stabilizer (family P) v)) (inclusion_injective _)
  let Γ := family P
  let H := graphLocalGroup Γ v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  dsimp only
  intro ρ hact hf ⟨S,hnat⟩
  have hcardV : Nat.card (Z Γ v) = Nat.card F ^ 2 := by
    have hh := hnat.1
    change Nat.card (Z Γ v) = 2^(2*n) at hh
    rw [hh,hF,←pow_mul,Nat.mul_comm n 2]
  refine ⟨hcardV,?_⟩
  obtain ⟨T,hT,_⟩ := linear_neighbor_core_sylow_image h hB hS hvw hne e
  have hquad : IsQuadratic ρ T := by
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) S T
    exact SL2SylowFixedRecognition.quadratic_conjugate ρ hnat.2.2 g
  have hnatT : IsSourceNatural ρ T n := ⟨hnat.1,hnat.2.1,hquad⟩
  obtain ⟨_,hcard,hfix,_⟩ := sourceNatural_coordinates_and_consequences ρ hf T hn hF hnatT
  have hZwZv : Z Γ w ≤ Z Γ v := hz ▸ intrinsic_local_omega_le_neighbor_Z h hB hS hvw.symm
  let U : Submodule (ZMod 2) (Additive (Z Γ v)) :=
    AddSubgroup.toZModSubmodule 2 ((Z Γ w).subgroupOf (Z Γ v)).toAddSubgroup
  have hUfixed : U ≤ fixedSpace ρ T := by
    intro z hz' t
    obtain ⟨l,hl,he⟩ := show t.val ∈ ((Q Γ w).subgroupOf H).map q from hT.symm ▸ t.property
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((ρ t.val z).toMul : G) = z.toMul
    rw [←he,hact]
    have hcz := (CommutingNontrivial.Z_centralizes_Q Γ w (source_Z_Q_U h w).1) hz'
    exact mul_inv_eq_iff_eq_mul.mpr (hcz l hl)
  have hupper := neighbor_center_core_displacement h hB hS hvw q T hT ρ hact hquad
  have hrange (t : SL(2,F)) (ht : t ∈ (T : Subgroup SL(2,F))) :
      LinearMap.range (ρ t - LinearMap.id) ≤ U := by
    rintro _ ⟨z,rfl⟩
    obtain ⟨l,hl,he⟩ := show t ∈ ((Q Γ w).subgroupOf H).map q from hT.symm ▸ ht
    change (((ρ t z - z).toMul : Z Γ v) : G) ∈ Z Γ w
    rw [toMul_sub,div_eq_mul_inv]
    change ((ρ t z).toMul : G) * (z.toMul : G)⁻¹ ∈ Z Γ w
    rw [←he,hact]
    exact hupper (commutator_mem_commutator hl z.toMul.property)
  have hcT : Nat.card T = 2^n := (Nat.card_congr
    (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv).trans hF
  have hneT : (T : Subgroup SL(2,F)) ≠ ⊥ := by
    intro he
    change Nat.card (T : Subgroup SL(2,F)) = 2^n at hcT
    rw [he,card_bot] at hcT
    have hp : 1 < 2^n := one_lt_pow₀ (by decide) (by omega)
    omega
  obtain ⟨t,ht,ht1⟩ := (T : Subgroup SL(2,F)).bot_or_exists_ne_one.resolve_left hneT
  have hdim : Module.finrank (ZMod 2) (Additive (Z Γ v)) = 2*n := by
    have hh := hnat.1
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hh
    exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hh
  have hdF : Module.finrank (ZMod 2) (fixedSpace ρ T) = n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hcard
    exact Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hcard
  have hfull : U = fixedSpace ρ T := by
    apply Submodule.eq_of_le_of_finrank_le hUfixed
    have hadd := fixedCodim_add_finrank ρ (zpowers t)
    rw [hfix t ht ht1,hdF,hdim,fixedCodim_zpowers_eq_displacement_rank] at hadd
    change Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) + n = 2*n at hadd
    rw [hdF]
    exact (show n = Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) by omega).trans_le
      (Submodule.finrank_mono (hrange t ht))
  have hcU : Nat.card U = Nat.card (Z Γ w) :=
    Nat.card_congr (subgroupOfEquivOfLe hZwZv).toEquiv
  rw [←hcU,hfull,hcard,hF]

private theorem cube_card_of_spanning_centers (A B C W D : Subgroup G) [Finite W] [IsMulCommutative W]
    {q : ℕ} (hq : 0 < q) (hAW : A ≤ W) (hBW : B ≤ W) (hCA : C ≤ A) (hCB : C ≤ B)
    (hA : Nat.card A = q^2) (hB : Nat.card B = q^2) (hC : Nat.card C = q)
    (hfixed : B ≤ centralizer (D : Set G))
    (hi : (centralizer (D : Set G)).relIndex W = q) (hs : W = A ⊔ B) :
    Nat.card W = q^3 ∧ W ⊓ centralizer (D : Set G) = B := by
  let : Finite A := Finite.of_injective (inclusion hAW) (inclusion_injective _)
  let : Finite B := Finite.of_injective (inclusion hBW) (inclusion_injective _)
  let E := W ⊓ centralizer (D : Set G)
  let : Finite E := Finite.of_injective (inclusion (show E ≤ W from inf_le_left)) (inclusion_injective _)
  have hBE : B ≤ E := le_inf hBW hfixed
  have hcE : q^2 ≤ Nat.card E := hB ▸ Nat.card_le_card_of_injective
    (inclusion hBE) (inclusion_injective _)
  have hiCB : C.relIndex B = q := by
    have hh := relIndex_mul_card_of_le hCB
    rw [hB,hC,pow_two] at hh
    nlinarith
  have hn : A ≤ normalizer (B : Set G) := (hAW.trans (le_centralizer W)).trans
    ((centralizer_le hBW).trans (Subgroup.centralizer_le_normalizer _))
  have hiAW : A.relIndex W ≤ q := by
    rw [hs,sup_comm,relIndex_sup_of_normalizes B A hn]
    have hh := relIndex_le_of_le_left (L := B) hCA (by rw [hiCB]; omega)
    exact hh.trans_eq hiCB
  have hcountA := relIndex_mul_card_of_le hAW
  rw [hA] at hcountA
  have hu : Nat.card W ≤ q^3 := calc
    Nat.card W = A.relIndex W * q^2 := hcountA.symm
    _ ≤ q * q^2 := Nat.mul_le_mul_right _ hiAW
    _ = q^3 := by ring
  have hcountE := relIndex_mul_card_of_le (show E ≤ W from inf_le_left)
  change (W ⊓ centralizer (D : Set G)).relIndex W * Nat.card E = Nat.card W at hcountE
  rw [inf_relIndex_left,hi] at hcountE
  have hl : q^3 ≤ Nat.card W := calc
    q^3 = q * q^2 := by ring
    _ ≤ q * Nat.card E := Nat.mul_le_mul_left _ hcE
    _ = Nat.card W := hcountE
  have hcW := le_antisymm hu hl
  refine ⟨hcW,(eq_of_le_of_card_ge hBE ?_).symm⟩
  rw [hB]
  rw [hcW] at hcountE
  nlinarith [hcE]

/-- The original F1.11 hypotheses construct both natural actions and the
opening 9.8 span decomposition. The exact order and centralizer follow
conditionally from the remaining geometric commutator containment. -/
theorem reduced_critical_commutator_span
    (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 =
      b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a,
      Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (htriv : ⁅V (Reduction.reducedFamily L S₀) beta 1 ⊓
      Q (Reduction.reducedFamily L S₀) a',
      V (Reduction.reducedFamily L S₀) a' 1⁆ = ⊥)
    (h8 : ∀ z : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj z a' →
      IsCriticalPair (Reduction.reducedFamily L S₀) z beta →
      ⁅Z (Reduction.reducedFamily L S₀) z,
        Z (Reduction.reducedFamily L S₀) beta⁆ = ⊥ →
      ⁅V (Reduction.reducedFamily L S₀) a' 1 ⊓
        Q (Reduction.reducedFamily L S₀) beta,
        V (Reduction.reducedFamily L S₀) beta 1⁆ ≠ ⊥ →
      ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        b (Reduction.reducedFamily L S₀) = 3 ∧
          Nonempty ((graphLocalGroup (Reduction.reducedFamily L S₀) z ⧸
            pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) z)) ≃*
              SL(2,F)))
    (hob : ∀ v w : Vertex (Reduction.reducedFamily L S₀),
      (graph (Reduction.reducedFamily L S₀)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily L S₀) v ≤ normalizer
        ((Q (Reduction.reducedFamily L S₀) w ⊓
          Q (Reduction.reducedFamily L S₀) v :
          Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    (Mα : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
    (Mβ : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)))
    (Mα' : BinaryRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a' ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a')))
    (Mαsource : IsRankOneModel (graphLocalGroup (Reduction.reducedFamily L S₀) a ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) a)))
 :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ a
    letI := Z_elementary Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1) a
    ∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (n : ℕ),
      0 < n ∧ Nat.card F = 2^n ∧
      ∃ eβ : (graphLocalGroup Γ beta ⧸
        pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F),
        (Q Γ a').relIndex (V Γ beta 1) = Nat.card F ∧
        (centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ beta 1) = Nat.card F ∧
        (centralizer (V Γ beta 1 : Set (Reduction.G₀ L S₀))).relIndex (V Γ a' 1) = Nat.card F ∧
        NaturalResidualSection h beta eβ n ∧
        ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (m : ℕ),
          0 < m ∧ Nat.card K = 2^m ∧
          ∃ eα : (H ⧸ pCore 2 H) ≃* SL(2,K),
            Nat.card K = Nat.card F ∧
            (¬ V Γ a' 1 ≤ Q Γ beta) ∧
            ⁅V Γ a' 1 ⊓ Q Γ beta,V Γ beta 1⁆ = ⊥ ∧
            (Q Γ beta).relIndex (V Γ a' 1) = Nat.card F ∧
            CriticalPathOrbit Γ a' ∧
            ⁅Q Γ beta,Z Γ a⁆ = Z Γ beta ∧ ⁅Q Γ beta,V Γ beta 1⁆ = Z Γ beta ∧
            Nat.card (Z Γ a) = Nat.card F ^ 2 ∧ Nat.card (Z Γ beta) = Nat.card F ∧
            (∃ x : Vertex Γ, (graph Γ).Adj beta x ∧ (graph Γ).dist x a' + 2 = b Γ ∧
              ∃ g : graphLocalGroup Γ beta, (g : Reduction.G₀ L S₀) • x = a ∧
                let R := ⁅V Γ beta 1,V Γ a' 1⁆
                V Γ beta 1 = R ⊔ R.map (MulAut.conj (g : Reduction.G₀ L S₀)).toMonoidHom ⊔ Z Γ x ∧
                (R ≤ Z Γ x → V Γ beta 1 = Z Γ a ⊔ Z Γ x ∧
                  Nat.card (V Γ beta 1) = Nat.card F ^ 3 ∧
                  V Γ beta 1 ⊓ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀)) = Z Γ x)) ∧
            let q := eα.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
            letI : Algebra (ZMod 2) K := ZMod.algebra K 2
            ∃ (ρ : Representation (ZMod 2) SL(2,K) (Additive (Z Γ a)))
              (T : Sylow 2 SL(2,K)),
              (∀ (l : H) (z : Additive (Z Γ a)),
                ((ρ (q l) z).toMul : Reduction.G₀ L S₀) =
                  (l : Reduction.G₀ L S₀) * z.toMul * (l : Reduction.G₀ L S₀)⁻¹) ∧
              Function.Injective ρ ∧ IsSourceNatural ρ T m ∧
              ∃ E : Additive (Z Γ a) ≃ₗ[ZMod 2] (Fin 2 → K),
                ∀ g z, E (ρ g z) = Matrix.mulVec g.val (E z) := by
  obtain ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,hC,hC',hres,
      K,instK,finK,charK,m,hm,hK,eα,heq,he,hrev,hi,hpath,hcQ,hcV,hnat⟩ :=
    reduced_critical_reciprocal_sections h hc hab hd hb hcomm htriv h8 hob Mα Mβ Mα' Mαsource
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := Z_elementary Γ (fun v => (source_Z_Q_U ht v).1) a
  obtain ⟨ρ,T,hact,hfaith,hna,E,hE⟩ := hnat
  have hB := Reduction.reduced_borel_core_sylow h
  have hS := Reduction.reduced_vertex_sylow h
  have hZ := fun z => (source_Z_Q_U ht z).1
  have hSyl := Reduction.reduced_kernel_sylow h
  obtain ⟨_,hb3,hω,_⟩ := Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm
  have hb2 : 2 < b Γ := by change 3 ≤ b Γ at hb3; omega
  obtain ⟨hca,hcb⟩ := linear_natural_neighbor_center_orders ht hB hS hab
    (core_escape_of_intersection_obstruction Γ (hob beta a hab.symm)) hω hm hK eα
    ρ hact hfaith ⟨T,hna⟩
  change Nat.card (Z Γ a) = Nat.card K ^ 2 at hca
  change Nat.card (Z Γ beta) = Nat.card K at hcb
  rw [heq] at hca hcb
  obtain ⟨x,hbx,hdx,g,hgx,hspan,hwhole⟩ := reduced_linear_commutator_span h hc hab hd hb hcomm eβ hi hcV
  change graphLocalGroup Γ beta at g
  change (graph Γ).Adj beta x at hbx
  change (graph Γ).dist x a' + 2 = b Γ at hdx
  change (g : Reduction.G₀ L S₀) • x = a at hgx
  have hcx : Nat.card (Z Γ x) = Nat.card F ^ 2 := by
    have hh := card_map_of_injective (K := Z Γ x)
      (f := (MulAut.conj (g : Reduction.G₀ L S₀)).toMonoidHom)
      (MulAut.conj (g : Reduction.G₀ L S₀)).injective
    rw [←Z_translate,hgx] at hh
    exact hh.symm.trans hca
  have hcaV : Z Γ a ≤ V Γ beta 1 := CommutingNontrivial.Z_neighbor_le_V Γ hab.symm
  have hcxV : Z Γ x ≤ V Γ beta 1 := CommutingNontrivial.Z_neighbor_le_V Γ hbx
  have hZA : Z Γ beta ≤ Z Γ a := hω ▸ intrinsic_local_omega_le_neighbor_Z ht hB hS hab.symm
  have hZX : Z Γ beta ≤ Z Γ x := hω ▸ intrinsic_local_omega_le_neighbor_Z ht hB hS hbx
  have hDQ : V Γ a' 1 ≤ Q Γ x := by
    apply iSup_le
    intro z
    apply iSup_le
    intro hz
    apply Z_le_Q_of_dist_lt_b Γ hZ hSyl z x
    have hz' := (mem_ball_iff Γ ht.generate a' z 1).mp hz
    have hh := (connected Γ ht.generate).dist_triangle (u := z) (v := a') (w := x)
    rw [SimpleGraph.dist_comm (u := z) (v := a'),SimpleGraph.dist_comm (u := a') (v := x)] at hh
    omega
  have hfixed : Z Γ x ≤ centralizer (V Γ a' 1 : Set (Reduction.G₀ L S₀)) :=
    (CommutingNontrivial.Z_centralizes_Q Γ x (hZ x)).trans (centralizer_le hDQ)
  let : Finite (V Γ beta 1) := Finite.of_injective
    (inclusion ((V_le_Q Γ ht.generate hZ hSyl beta (r := 1) hb).trans (Q_le_stabilizer Γ beta)))
    (inclusion_injective _)
  let := V_elementary Γ ht.generate hZ hSyl beta (r := 1) (by simpa using hb2)
  refine ⟨F,instF,finF,charF,n,hn,hF,eβ,hx,hC,hC',hres,
    K,instK,finK,charK,m,hm,hK,eα,heq,he,hrev,hi,hpath,hcQ,hcV,hca,hcb,
    ⟨x,hbx,hdx,g,hgx,hspan,?_⟩,ρ,T,hact,hfaith,hna,E,hE⟩
  intro hR
  have hw := hwhole hR
  exact ⟨hw,cube_card_of_spanning_centers (Z Γ a) (Z Γ x) (Z Γ beta) (V Γ beta 1) (V Γ a' 1)
    Nat.card_pos hcaV hcxV hZA hZX hca hcx hcb hfixed hC hw⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
