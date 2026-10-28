module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.CommutatorCentralizer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborFixedLine
public import Theory.Representation.BinaryConjugationSection.InvariantImages

/-!
# Two neighboring centers in the natural residual section

Two distinct neighboring cores generate the actual local linear quotient.
Their neighboring centers consequently fill complementary natural Sylow fixed
lines. The exact center orders identify the residual kernel on their product
with the central omega and give this product order q^3.

A normal subgroup contained in that product has either zero or full image in
the irreducible natural section. In the full case the original core commutator
contains the central omega; local conjugate generation then makes the subgroup
and the two-center product equal the entire neighborhood span. No splitting of
the residual extension is assumed. The geometric commutator application is in
CommutatorDichotomy, and the whole-span application is in WholeSpan.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
9.3(c), 9.4(a)--(c), and the last paragraph of 9.8, printed pp.142--143,146.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem neighbor_core_index
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v w : Vertex (family P)} (hv : (graph (family P)).Adj v w)
    (hne : ¬ Q (family P) w ≤ Q (family P) v)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) v ⧸ pCore 2 (graphLocalGroup (family P) v)) ≃* SL(2,F)) :
    (Q (family P) v).relIndex (Q (family P) w) = Nat.card F := by
  let H := graphLocalGroup (family P) v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  obtain ⟨T,hT,_⟩ := linear_neighbor_core_sylow_image h hB hS hv hne e
  have hk : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkmap : q.ker.map H.subtype = Q (family P) v := hk ▸ graphLocalGroup_core h v
  have hh := relIndex_ker ((Q (family P) w).subgroupOf H) q
  rw [←relIndex_map_map_of_injective _ _ H.subtype_injective,hkmap,
    map_subgroupOf_eq_of_le (neighbor_core_le_localGroup h hB hS hv),hT] at hh
  exact hh.trans (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv)

/-- Two distinct neighboring cores generate the local linear group modulo its core. -/
theorem linear_neighbor_core_generation
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {w v r : Vertex (family P)} (hv : (graph (family P)).Adj w v)
    (hr : (graph (family P)).Adj w r) (hne : v ≠ r)
    (hve : ¬ Q (family P) v ≤ Q (family P) w)
    (hre : ¬ Q (family P) r ≤ Q (family P) w)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,F)) :
    graphLocalGroup (family P) w = Q (family P) w ⊔ Q (family P) v ⊔ Q (family P) r := by
  exact linear_local_two_actor_generation h hB hS hv hr hne e _ _
    (neighbor_core_le_localGroup h hB hS hv) (neighbor_core_le_localGroup h hB hS hr)
    (isPGroup_pCoreIn 2 _) (isPGroup_pCoreIn 2 _)
    (neighbor_core_index h hB hS hv hve e) (neighbor_core_index h hB hS hr hre e)
    (Q_le_stabilizer _ _) (Q_le_stabilizer _ _)

/-- Distinct neighboring centers fill complementary lines in the literal
natural residual section. -/
theorem natural_residual_neighbor_pair_images
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {w v r : Vertex (family P)} (hv : (graph (family P)).Adj w v)
    (hr : (graph (family P)).Adj w r) (hne : v ≠ r)
    (hve : ¬ Q (family P) v ≤ Q (family P) w)
    (hre : ¬ Q (family P) r ≤ Q (family P) w)
    (hz : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,F))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection (graphLocalGroup (family P) w) (V (family P) w 1)
      (V (family P) w 1 ⊓ centralizer ((pResidual 2 (graphLocalGroup (family P) w)).map
        (graphLocalGroup (family P) w).subtype : Set G))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) w))))))
    (hf : Function.Injective σ) (T : Sylow 2 SL(2,F))
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) (hnat : IsSourceNatural σ T n) :
    IsCompl (c.imageSpace (Z (family P) v)) (c.imageSpace (Z (family P) r)) := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ w
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  obtain ⟨Tv,hTv,hIv,_,hfixv⟩ := residual_neighbor_fixed_line h hB hS hv hve hz e σ c hf T hn hF hnat
  obtain ⟨Tr,hTr,hIr,_,_⟩ := residual_neighbor_fixed_line h hB hS hr hre hz e σ c hf T hn hF hnat
  have hneT : Tv ≠ Tr := by
    intro he
    have hQr : Q Γ r ≤ stabilizer Γ v := by
      intro x hx
      let l : H := ⟨x,neighbor_core_le_localGroup h hB hS hr hx⟩
      apply (hfixv l).mp
      apply (Tv : Subgroup SL(2,F)).le_normalizer
      rw [he,←hTr]
      exact mem_map_of_mem q hx
    have hH : H ≤ stabilizer Γ v := by
      change graphLocalGroup (family P) w ≤ stabilizer Γ v
      rw [linear_neighbor_core_generation h hB hS hv hr hne hve hre e]
      exact sup_le (sup_le ((source_Z_Q_U h w).2.trans
        ((ballKernel_one_le_edge Γ hv).trans inf_le_right)) (Q_le_stabilizer Γ v)) hQr
    obtain ⟨g,hg,hgv⟩ := graphLocalGroup_transitive h hB hS w ⟨v,hv⟩ ⟨r,hr⟩
    exact hne ((hH hg).symm.trans hgv)
  have hquad : IsQuadratic σ Tv := by
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq SL(2,F) T Tv
    exact SL2SylowFixedRecognition.quadratic_conjugate σ hnat.2.2 g
  let : Finite (V Γ w 1) := Finite.of_injective
    (inclusion (c.section_le.trans (sylowGenerated_le _))) (inclusion_injective _)
  let : Finite W := Finite.of_surjective (fun x => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  obtain ⟨hgen,hfix,_⟩ := sourceNatural_generation_and_fixed σ hf Tv hn hF ⟨hnat.1,hnat.2.1,hquad⟩
  rw [hIv,hIr]
  exact sl2_sylow_fixed_isCompl σ Tv Tr hneT hquad hgen hfix

private theorem kernel_inf_sup_of_disjoint_images
    {H S K : Subgroup G} [IsMulCommutative S]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) H W} (c : BinaryConjugationSection H S K ρ)
    (A B Z₀ : Subgroup G) (hA : A ≤ S) (hB : B ≤ S)
    (hKA : A ⊓ K = Z₀) (hKB : B ⊓ K = Z₀)
    (hi : Disjoint (c.imageSpace A) (c.imageSpace B)) :
    (A ⊔ B) ⊓ K = Z₀ := by
  apply le_antisymm ?_ (hKA ▸ (show A ⊓ K ≤ (A ⊔ B) ⊓ K from inf_le_inf_right _ le_sup_left))
  rintro x ⟨hx,hxK⟩
  have hn : A ≤ normalizer (B : Set G) :=
    (hA.trans (le_centralizer S)).trans ((centralizer_le hB).trans (Subgroup.centralizer_le_normalizer _))
  change x ∈ (↑(A ⊔ B) : Set G) at hx
  rw [coe_mul_of_left_le_normalizer_right A B hn] at hx
  obtain ⟨a,ha,b,hb,rfl⟩ := hx
  let aS : S := ⟨a,hA ha⟩
  let bS : S := ⟨b,hB hb⟩
  have hab : c.coordinates aS * c.coordinates bS = 1 := by
    rw [←map_mul]
    exact (c.coordinates_eq_one_iff (aS*bS)).mpr hxK
  have ha0 : (c.coordinates aS).toAdd = 0 := by
    have haI : (c.coordinates aS).toAdd ∈ c.imageSpace A :=
      (c.mem_imageSpace_iff A _).mpr ⟨aS,ha,rfl⟩
    have hbI : (c.coordinates aS).toAdd ∈ c.imageSpace B := by
      have he : (c.coordinates aS).toAdd = -(c.coordinates bS).toAdd := by
        exact eq_neg_of_add_eq_zero_left (congrArg Multiplicative.toAdd hab)
      rw [he]
      exact (c.imageSpace B).neg_mem ((c.mem_imageSpace_iff B _).mpr ⟨bS,hb,rfl⟩)
    exact (Submodule.disjoint_def.mp hi) _ haI hbI
  have hb0 : c.coordinates bS = 1 := by
    have ha1 : c.coordinates aS = 1 := ha0
    simpa only [ha1,one_mul] using hab
  exact Z₀.mul_mem (hKA ▸ ⟨ha,(c.coordinates_eq_one_iff aS).mp ha0⟩)
    (hKB ▸ ⟨hb,(c.coordinates_eq_one_iff bS).mp hb0⟩)

private theorem fixed_line_kernel_of_orders
    (A K Z₀ : Subgroup G) [Finite A] {q : ℕ} (hq : 0 < q)
    (hZA : Z₀ ≤ A) (hZK : Z₀ ≤ K)
    (hA : Nat.card A = q^2) (hZ : Nat.card Z₀ = q) (hi : K.relIndex A = q) :
    A ⊓ K = Z₀ := by
  let : Finite (A ⊓ K : Subgroup G) := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hh := relIndex_mul_card_of_le (show A ⊓ K ≤ A from inf_le_left)
  rw [inf_relIndex_left,hi,hA] at hh
  have he : Nat.card (A ⊓ K : Subgroup G) = q := by nlinarith
  exact (eq_of_le_of_card_ge (le_inf hZA hZK) (by rw [he,hZ])).symm

/-- The residual kernel on two neighboring centers is exactly the central
omega. Both centers retain their literal subgroup coordinates. -/
theorem natural_residual_neighbor_pair_kernel
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {w v r : Vertex (family P)} (hv : (graph (family P)).Adj w v)
    (hr : (graph (family P)).Adj w r) (hne : v ≠ r)
    (hve : ¬ Q (family P) v ≤ Q (family P) w)
    (hre : ¬ Q (family P) r ≤ Q (family P) w)
    (hz : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,F))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection (graphLocalGroup (family P) w) (V (family P) w 1)
      (V (family P) w 1 ⊓ centralizer ((pResidual 2 (graphLocalGroup (family P) w)).map
        (graphLocalGroup (family P) w).subtype : Set G))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) w))))))
    (hf : Function.Injective σ) (T : Sylow 2 SL(2,F))
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) (hnat : IsSourceNatural σ T n)
    (hcv : Nat.card (Z (family P) v) = Nat.card F ^ 2)
    (hcw : Nat.card (Z (family P) w) = Nat.card F)
    [IsMulCommutative (V (family P) w 1)] :
    let K := V (family P) w 1 ⊓ centralizer ((pResidual 2 (graphLocalGroup (family P) w)).map
      (graphLocalGroup (family P) w).subtype : Set G)
    (Z (family P) v ⊔ Z (family P) r) ⊓ K = Z (family P) w ∧
      c.imageSpace (Z (family P) v ⊔ Z (family P) r) = ⊤ ∧
      Nat.card (Z (family P) v ⊔ Z (family P) r : Subgroup G) = Nat.card F ^ 3 := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ w
  let K := V Γ w 1 ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G)
  have hvV := CommutingNontrivial.Z_neighbor_le_V Γ hv
  have hrV := CommutingNontrivial.Z_neighbor_le_V Γ hr
  have hZK : Z Γ w ≤ K := le_inf (Z_le_V Γ w 1) (by
    intro x hx
    exact centralizer_le (map_subtype_le _) ((mem_omegaCenterIn_iff _ _).mp (hz ▸ hx)).2.1)
  have hind (x : Vertex Γ) (hx : (graph Γ).Adj w x) (he : ¬ Q Γ x ≤ Q Γ w) :
      K.relIndex (Z Γ x) = Nat.card F := by
    obtain ⟨_,_,_,hi,_⟩ := residual_neighbor_fixed_line h hB hS hx he hz e σ c hf T hn hF hnat
    have hi' : K.relIndex (Z Γ x) =
        (centralizer ((pResidual 2 H).map H.subtype : Set G)).relIndex (Z Γ x) := by
      apply congrArg Subgroup.index
      ext z
      exact and_iff_right (CommutingNontrivial.Z_neighbor_le_V Γ hx z.property)
    exact hi'.trans hi
  obtain ⟨g,hg,hgr⟩ := graphLocalGroup_transitive h hB hS w ⟨v,hv⟩ ⟨r,hr⟩
  have hcr : Nat.card (Z Γ r) = Nat.card F ^ 2 := by
    have hh := card_map_of_injective (K := Z Γ v)
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    rw [←Z_translate,hgr] at hh
    exact hh.trans hcv
  have hker (x : Vertex Γ) (hx : (graph Γ).Adj w x) (he : ¬ Q Γ x ≤ Q Γ w)
      (hcx : Nat.card (Z Γ x) = Nat.card F ^ 2) : Z Γ x ⊓ K = Z Γ w := by
    let : Finite (Z Γ x) := Finite.of_injective (inclusion (Z_le_stabilizer Γ x)) (inclusion_injective _)
    exact fixed_line_kernel_of_orders _ _ _ Nat.card_pos
      (hz ▸ intrinsic_local_omega_le_neighbor_Z h hB hS hx) hZK hcx hcw (hind x hx he)
  have hp := natural_residual_neighbor_pair_images h hB hS hv hr hne hve hre hz e σ c hf T hn hF hnat
  have hk := kernel_inf_sup_of_disjoint_images c _ _ _ hvV hrV (hker v hv hve hcv)
    (hker r hr hre hcr) hp.disjoint
  have hi : c.imageSpace (Z Γ v ⊔ Z Γ r) = ⊤ := by
    apply top_unique
    rw [←hp.sup_eq_top]
    exact sup_le (c.imageSpace_mono le_sup_left) (c.imageSpace_mono le_sup_right)
  refine ⟨hk,hi,?_⟩
  have hcard := c.imageSpace_card_eq_relIndex (Z Γ v ⊔ Z Γ r) (sup_le hvV hrV)
  have hcW : Nat.card W = Nat.card F ^ 2 := by
    rw [hnat.1,hF,←pow_mul,Nat.mul_comm n 2]
  rw [hi,Nat.card_congr (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) W) ≃ₗ[ZMod 2] W).toEquiv,hcW] at hcard
  have hh := relIndex_mul_card_of_le (show (Z Γ v ⊔ Z Γ r) ⊓ K ≤ Z Γ v ⊔ Z Γ r from inf_le_left)
  rw [inf_relIndex_left,←hcard,hk,hcw] at hh
  exact hh.symm.trans (by ring)

/-- A local normal subgroup contained in two neighboring centers is either
central or the whole neighborhood span. The latter also proves the whole-span
identity, without assuming a splitting of the residual extension. -/
theorem natural_residual_normal_pair_dichotomy
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {w v r : Vertex (family P)} (hv : (graph (family P)).Adj w v)
    (hr : (graph (family P)).Adj w r) (hne : v ≠ r)
    (hve : ¬ Q (family P) v ≤ Q (family P) w)
    (hre : ¬ Q (family P) r ≤ Q (family P) w)
    (hz : Z (family P) w = omegaCenterIn (graphLocalGroup (family P) w))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup (family P) w ⧸ pCore 2 (graphLocalGroup (family P) w)) ≃* SL(2,F))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL(2,F) W)
    (c : BinaryConjugationSection (graphLocalGroup (family P) w) (V (family P) w 1)
      (V (family P) w 1 ⊓ centralizer ((pResidual 2 (graphLocalGroup (family P) w)).map
        (graphLocalGroup (family P) w).subtype : Set G))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (graphLocalGroup (family P) w))))))
    (hf : Function.Injective σ) (T : Sylow 2 SL(2,F))
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n) (hnat : IsSourceNatural σ T n)
    (hcv : Nat.card (Z (family P) v) = Nat.card F ^ 2)
    (hcw : Nat.card (Z (family P) w) = Nat.card F)
    (hcore : ⁅Q (family P) w,Z (family P) v⁆ = Z (family P) w)
    [IsMulCommutative (V (family P) w 1)]
    (D : Subgroup G) (hD : D ≤ Z (family P) v ⊔ Z (family P) r)
    (hnD : graphLocalGroup (family P) w ≤ normalizer (D : Set G)) :
    D ≤ Z (family P) w ∨
      D = V (family P) w 1 ∧ V (family P) w 1 = Z (family P) v ⊔ Z (family P) r := by
  let := finite_endpoints h
  let Γ := family P
  let H := graphLocalGroup Γ w
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let K := V Γ w 1 ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G)
  let N := Z Γ v ⊔ Z Γ r
  have hNV : N ≤ V Γ w 1 := sup_le (CommutingNontrivial.Z_neighbor_le_V Γ hv)
    (CommutingNontrivial.Z_neighbor_le_V Γ hr)
  have hDV : D ≤ V Γ w 1 := hD.trans hNV
  obtain ⟨hker,_⟩ := natural_residual_neighbor_pair_kernel h hB hS hv hr hne hve hre hz e σ c hf T hn hF hnat hcv hcw
  let : Finite (V Γ w 1) := Finite.of_injective
    (inclusion (c.section_le.trans (sylowGenerated_le _))) (inclusion_injective _)
  let : Finite W := Finite.of_surjective (fun x => (c.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  let := (sourceNatural_generation_and_fixed σ hf T hn hF hnat).2.2
  let I : Subrepresentation σ := {
    toSubmodule := c.imageSpace D
    apply_mem_toSubmodule g := by
      intro z hz'
      obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective _)) g
      exact c.imageSpace_apply_mem D l (hnD l.property) z hz' }
  rcases eq_bot_or_eq_top I with hzero | hfull
  · left
    intro x hx
    have hm : (c.coordinates ⟨x,hDV hx⟩).toAdd ∈ I :=
      (c.mem_imageSpace_iff D _).mpr ⟨⟨x,hDV hx⟩,hx,rfl⟩
    rw [hzero] at hm
    exact hker ▸ ⟨hD hx,(c.coordinates_eq_one_iff _).mp hm⟩
  · right
    have hcover : N ≤ D ⊔ Z Γ w := by
      intro x hx
      have hm : (c.coordinates ⟨x,hNV hx⟩).toAdd ∈ c.imageSpace D := by
        change (c.coordinates ⟨x,hNV hx⟩).toAdd ∈ I
        rw [hfull]
        trivial
      obtain ⟨d,hd,he⟩ := (c.mem_imageSpace_iff D _).mp hm
      have hk : ((d⁻¹ * ⟨x,hNV hx⟩ : V Γ w 1) : G) ∈ K := by
        apply (c.coordinates_eq_one_iff _).mp
        rw [map_mul,map_inv,Multiplicative.toAdd.injective he,inv_mul_cancel]
      have hz' : (d : G)⁻¹*x ∈ Z Γ w := hker ▸ ⟨N.mul_mem (N.inv_mem (hD hd)) hx,hk⟩
      simpa only [mul_inv_cancel_left] using (D ⊔ Z Γ w).mul_mem (mem_sup_left hd) (mem_sup_right hz')
    have hZwH : Z Γ w ≤ H := (Z_le_V Γ w 1).trans c.section_le
    have hND : ⁅N,Q Γ w⁆ ≤ D := by
      apply (commutator_mono hcover le_rfl).trans
      apply commutator_sup_le_of_relative_normal H D (Z Γ w) (Q Γ w) D hnD
        (hDV.trans c.section_le) hZwH
      · exact le_normalizer_iff_commutator_le_left.mp ((core_le_graphLocalGroup h w).trans hnD)
      · rw [commutator_eq_bot_iff_le_centralizer.mpr (CommutingNontrivial.Z_centralizes_Q Γ w (source_Z_Q_U h w).1)]
        exact bot_le
    have hZD : Z Γ w ≤ D := by
      rw [←hcore,commutator_comm]
      exact (commutator_mono le_sup_left le_rfl).trans hND
    have hND' : N ≤ D := hcover.trans (sup_le le_rfl hZD)
    have hspan := CommutingThreeProfile.V_eq_center_sup_neighbor_conjugates Γ H (sylowGenerated_le _) hv
      (fun x hx => graphLocalGroup_transitive h hB hS w ⟨v,hv⟩ ⟨x,hx⟩)
    have hVD : V Γ w 1 ≤ D := hspan.le.trans
      (sup_le hZD (conjugateSpanBy_le (le_sup_left.trans hND') hnD))
    exact ⟨le_antisymm hDV hVD,le_antisymm (hVD.trans hD) hNV⟩


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
