module
public import Theory.Representation.RankOne.QuadraticRecognition.DihedralSmallSeed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.DihedralCoreProduct
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCoreProduct
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearCoreProduct
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralExclusion
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearCoreProduct

/-!
# Excluding the original D10 neighbor row

In the central-intersection alternative, H = V_x ∩ V_y is Z_m.
Its image C in the literal quotient V_y/Z_y has order two. The original
D10 marking sends V_x to a nontrivial elementary actor B, which fixes C
and has all displacements in C. Local transitivity makes the conjugates
of C generate the quotient. DihedralSmallSeed makes the action trivial,
contradicting the original critical pair. Thus H is not central in Q_m.

The common Sylow has quotient order two, so the nontrivial image of V_x
fills it. This gives the exact index and Q_m = V_x (Q_y ∩ Q_m), hence
also the middle-core product. The previously proved minimal-center and
center-free argument now makes H central in Q_m, excluding the D10 row.
Before that final contradiction, the source commutator application retains
all four reduced/original identities, including the literal original
parabolic core and starred inclusion.

The common Sylows, field order two, natural-center orders and minimality,
centerlessness, commutator bounds and conjugated indices remain genuine
earlier Chapter 8 inputs. The full linear/binary cases and (12.9)/(13.1)
assembly still belong to this theorem family. This module excludes the
D10 neighbor under those inputs; it does not assert the full classification.
The private quotient-image and critical-action lemmas are reused within
this theorem family without changing their original public boundaries.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1), (12.3)(a--d), (12.4)(a), printed pp.178--181.
-/

@[expose] public noncomputable section


open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The literal D10 quotient and critical geometry exclude a central intersection. -/
theorem source_dihedral_intersection_not_central
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (eD : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* DihedralGroup 5)
    (hfield : Nat.card k = 2)
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a) :
    ¬ V (reducedFamily L S) x 1 ⊓
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ≤
        centralizer (Q (reducedFamily L S) (base (reducedFamily L S) i) : Set (G₀ L S)) := by
  intro hcentral
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let A := star L S (!i)
  let D := V F y 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hgen : F false ⊔ F true = ⊤ := (reduced_triple h).generate
  have hZ : ∀ v : Vertex F, Z F v ≤ omegaCenterIn (Q F v) :=
    fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hSyl : ∀ v, ∃ T : Sylow 2 (U F v),
      (T : Subgroup (U F v)).map (U F v).subtype = Q F v := reduced_kernel_sylow h
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  let := V_elementary F hgen hZ hSyl hb y
  let : ((Z F y).subgroupOf D).Normal := normal_of_isMulCommutative _
  let π := QuotientGroup.mk' ((Z F y).subgroupOf D)
  let C := ((Z F m).subgroupOf D).map π
  let : Finite D := Finite.of_injective
    (inclusion ((V_le_Q F hgen hZ hSyl hb y).trans
      (Q_le_stabilizer F y))) (inclusion_injective _)
  obtain ⟨hC, hbound, _, _⟩ := source_central_intersection_layer_bound h i hb hxadj hne
    T R hT hR e hz hcard hcardy hzx hzy hcommx hcommy hcentral hcross hsmall hactor
  obtain ⟨ρ,hρ⟩ := exists_center_layer_action F hgen hZ
    hSyl hb y A (star_le_stabilizer (!i)) (star_core h (!i)).le hcommy
  obtain ⟨g,hg,hgy⟩ := star_locally_transitive h i hadj hxadj
  have hρne := center_layer_action_nontrivial F hgen hZ
    hSyl hb hc hxa hadj.symm A (star_le_stabilizer (!i))
    (fun z hz => star_locally_transitive h (!i) hadj.symm hz)
    g (star_le_stabilizer i hg) hgy hzy ρ hρ
  let eA := (originalQuotient h (!i)).symm.trans eD
  let τ := ρ.comp eA.symm.toMonoidHom
  let q := eA.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  let B := ((V F x 1).subgroupOf A).map q
  have hVm : V F x 1 ≤ Q F m := V_le_neighbor_Q F hgen hZ hSyl hb hxadj.symm
  have hQA : Q F m ≤ A := (le_sup_left.trans hRy.ge).trans (map_subtype_le _)
  have hVA : V F x 1 ≤ A := hVm.trans hQA
  let := V_elementary F hgen hZ hSyl hb x
  let : IsElementaryAbelian 2 ((V F x 1).subgroupOf A) := IsElementaryAbelian.subgroupOf hVA
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map q
  have hBne : B ≠ ⊥ := by
    intro he
    have hh := (map_eq_bot_iff ((V F x 1).subgroupOf A)).mp he
    have hk : q.ker = (Q F y).subgroupOf A := by
      have hq : q.ker = pCore 2 A := by
        ext v
        change eA (QuotientGroup.mk' (pCore 2 A) v) = 1 ↔ v ∈ pCore 2 A
        rw [map_eq_one_iff _ eA.injective]
        exact QuotientGroup.eq_one_iff v
      rw [hq, ← star_core h (!i)]
      exact (comap_map_eq_self_of_injective A.subtype_injective (pCore 2 A)).symm
    rw [hk] at hh
    have hescape : ¬ V F x 1 ≤ Q F y := by
      intro he
      have hseed : Z F a ≤ V F x 1 :=
        le_iSup_of_le _ (le_iSup_of_le ((mem_ball_one F _ _).mpr (Or.inl hxa)) le_rfl)
      exact hc.2 (hseed.trans (he.trans (source_Z_Q_U (reduced_triple h) y).2))
    exact hescape (fun v hv => hh (show (⟨v,hVA hv⟩ : A) ∈ (V F x 1).subgroupOf A from hv))
  have hτ (u : A) : τ (q u) = ρ (QuotientGroup.mk u) := by
    change ρ (eA.symm (eA (QuotientGroup.mk u))) = _
    rw [eA.symm_apply_apply]
  have hmov : subspaceCommutator τ ⊤ B ≤ binarySpace C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t,ht,v,_,rfl⟩
    obtain ⟨u,hu,rfl⟩ := ht
    obtain ⟨d,hd⟩ := QuotientGroup.mk'_surjective ((Z F y).subgroupOf D) v.toMul
    have hv : v = Additive.ofMul (π d) := (congrArg Additive.ofMul hd).symm
    rw [hv]
    change (τ (q u) (Additive.ofMul (π d))).toMul / (π d) ∈ C
    rw [div_eq_mul_inv,hτ]
    change (ρ (QuotientGroup.mk u) (Additive.ofMul (QuotientGroup.mk d))).toMul * (π d)⁻¹ ∈ C
    rw [hρ u d]
    change π _ * (π d)⁻¹ ∈ C
    rw [← map_inv, ← map_mul]
    apply hbound
    apply mem_map_of_mem
    change (u : G₀ L S) * d * (u : G₀ L S)⁻¹ * (d : G₀ L S)⁻¹ ∈ ⁅V F x 1,D⁆
    exact commutator_mem_commutator hu d.property
  have hZD : Z F m ≤ D :=
    le_iSup_of_le m (le_iSup_of_le ((mem_ball_one F y m).mpr (Or.inl hadj.symm)) le_rfl)
  have hZX : Z F m ≤ V F x 1 :=
    le_iSup_of_le m (le_iSup_of_le ((mem_ball_one F x m).mpr (Or.inl hxadj.symm)) le_rfl)
  have hfixed : binarySpace C ≤ fixedSpace τ B := by
    rintro v ⟨z,hz,rfl⟩ t
    have ht := t.property
    obtain ⟨u,hu,he⟩ := ht
    change τ t.val (Additive.ofMul (π z)) = Additive.ofMul (π z)
    rw [← he,hτ]
    apply Additive.toMul.injective
    change (ρ (QuotientGroup.mk u) (Additive.ofMul (QuotientGroup.mk z))).toMul =
      (QuotientGroup.mk z : D ⧸ (Z F y).subgroupOf D)
    rw [hρ u z]
    apply congrArg (fun d : D => (QuotientGroup.mk d : D ⧸ (Z F y).subgroupOf D))
    apply Subtype.ext
    let := V_elementary F hgen hZ hSyl hb x
    have hh : (u : G₀ L S) * z = (z : G₀ L S) * u :=
      congrArg Subtype.val (mul_comm (⟨u,hu⟩ : V F x 1) ⟨z,hZX hz⟩)
    change (u : G₀ L S) * z * (u : G₀ L S)⁻¹ = z
    rw [hh,mul_inv_cancel_right]
  have hseed : (⨆ a, (binarySpace C).map (τ a)) = ⊤ := by
    let M := ⨆ a, (binarySpace C).map (τ a)
    let B := (binarySubgroup M).comap π
    let J := B.map D.subtype
    have hDJ : D ≤ J := by
      change V F y 1 ≤ J
      rw [V_eq_center_sup_neighbor_conjugates F A (star_le_stabilizer (!i)) hadj.symm
        (fun z hz => star_locally_transitive h (!i) hadj.symm hz)]
      apply sup_le
      · intro z hz
        let d : D := ⟨z,Z_le_V F y 1 hz⟩
        refine ⟨d,?_,rfl⟩
        change π d ∈ binarySubgroup M
        have he : π d = 1 := (QuotientGroup.eq_one_iff d).mpr hz
        rw [he]
        exact one_mem _
      · apply (closure_le _).mpr
        rintro z ⟨a,ha,v,hv,rfl⟩
        let u : A := ⟨a,ha⟩
        let d : D := ⟨v,hZD hv⟩
        let w : D := ⟨a * v * a⁻¹,
          (mem_normalizer_iff.mp (star_normalizes_span h (!i) ha) v).mp (hZD hv)⟩
        refine ⟨w,?_,rfl⟩
        change Additive.ofMul (π w) ∈ M
        have he : τ (q u) (Additive.ofMul (π d)) = Additive.ofMul (π w) := by
          rw [hτ]
          exact congrArg Additive.ofMul (hρ u d)
        apply (le_iSup (fun a => (binarySpace C).map (τ a)) (q u))
        exact ⟨Additive.ofMul (π d),mem_map_of_mem π hv,he⟩
    apply top_unique
    intro v _
    obtain ⟨d,hd⟩ := QuotientGroup.mk'_surjective ((Z F y).subgroupOf D) v.toMul
    obtain ⟨w,hw,he⟩ := hDJ d.property
    have hwd : w = d := Subtype.ext he
    rw [hwd] at hw
    change Additive.ofMul (π d) ∈ M at hw
    have hvd : Additive.ofMul (π d) = v := congrArg Additive.ofMul hd
    exact hvd ▸ hw
  have hneτ : τ ≠ 1 := by
    intro ht
    apply hρne
    apply MonoidHom.ext
    intro z
    apply LinearMap.ext
    intro v
    have he := DFunLike.congr_fun (DFunLike.congr_fun ht (eA z)) v
    change ρ (eA.symm (eA z)) v = v at he
    change ρ z v = v
    simpa only [eA.symm_apply_apply] using he
  have hcardC : Nat.card (binarySpace C) ≤ 2 :=
    ((binarySubgroup_card (binarySpace C)).symm.trans (hC.trans hfield)).le
  exact hneτ (Representation.RankOne.QuadraticRecognition.dihedral_small_seed_trivial
    τ B hBne (binarySpace C) hfixed hseed hmov hcardC)

/-- The D10 middle-core product gives all four literal reduced/original commutator identities. -/
theorem source_dihedral_product_and_intersection_commutator
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (eD : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* DihedralGroup 5)
    (hfield : Nat.card k = 2)
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hnotcore : ¬ stabilizer (reducedFamily L S) (base (reducedFamily L S) i) ≤ normalizer
      ((Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊓
        Q (reducedFamily L S) (base (reducedFamily L S) i) : Subgroup (G₀ L S)) : Set (G₀ L S)))
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i)) :
    let F := reducedFamily L S
    let H := V F x 1 ⊓ V F (base F (!i)) 1
    Q F (base F i) = (Q F x ⊓ Q F (base F i)) ⊔
      (Q F (base F (!i)) ⊓ Q F (base F i)) ∧
    ⁅H, Q F (base F i)⁆ = Z F (base F i) ∧
      ⁅H.map (G₀ L S).subtype, (parabolic L S (if i then 1 else 0)).pCoreIn 2⁆ =
        (Z F (base F i)).map (G₀ L S).subtype ∧
      V F (base F (!i)) 1 = ⁅V F (base F (!i)) 1, star L S (!i)⁆ ∧
      (V F (base F (!i)) 1).map (G₀ L S).subtype =
        ⁅(V F (base F (!i)) 1).map (G₀ L S).subtype,
          starredParabolic L S (if !i then 1 else 0)⁆ := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let H := V F x 1 ⊓ V F y 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hnot := source_dihedral_intersection_not_central h i hb hxadj hne T R hT hR e
    hz hcard hcardy hzx hzy hcommx hcommy.le hcross hsmall hactor eD hfield Ry hRy hc hxa
  have hgen : star L S i = (Q F x ⊔ Q F y) ⊔ Q F m := by
    have hh := star_three_core_generation h i hxadj hne T R hT hR
    simpa only [sup_comm, sup_left_comm, sup_assoc] using hh
  have hindex : (Q F y ⊓ Q F m).relIndex (Q F m) = 2 := by
    simpa only [inf_comm] using source_dihedral_core_index h (!i) eD Ry hRy
  obtain ⟨g,hg,hgx⟩ := star_locally_transitive h i hadj hxadj
  have hxindex := (middle_core_intersection_index_conjugate F g
    (star_le_stabilizer i hg) hgx).trans hindex
  have hgen' : star L S i = (Q F y ⊔ Q F x) ⊔ Q F m := by
    simpa only [sup_comm, sup_left_comm, sup_assoc] using hgen
  obtain ⟨hp,_⟩ := middle_core_product_of_index_two F
    (fun v => (source_Z_Q_U (reduced_triple h) v).2) hadj.symm hxadj.symm
    (star L S i) hgen'
    (fun hn => hnotcore ((core_intersection_normalizer_transfer F hadj (star L S i)
      (star_le_stabilizer i) (fun z hz => star_locally_transitive h i hadj hz)).mpr hn))
    hindex hxindex
  have hprod : Q F m = (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m) := by
    simpa only [sup_comm] using hp
  have hnH : star L S i ≤ normalizer (H : Set (G₀ L S)) := by
    rw [hgen]
    exact intersection_normalized F (fun v => (source_Z_Q_U (reduced_triple h) v).2)
      hxadj.symm hadj.symm hcommx hcommy.le hzx hzy
  have hZA : Z F m ≤ star L S i :=
    ((hZ m).trans (map_subtype_le _)).trans
      ((star_core h i).ge.trans (map_subtype_le _))
  have hnZ : star L S i ≤ normalizer (Z F m : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans
      ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F m)).mp (Z_normal F m))
  let : ((Z F m).subgroupOf (star L S i)).Normal :=
    normal_subgroupOf_of_le_normalizer hnZ
  let : IsMinimalNormal ((Z F m).subgroupOf (star L S i)) :=
    ⟨fun N _ hN => hmin N inferInstance hN⟩
  have he : ⁅H,Q F m⁆ = Z F m :=
    (intersection_commutator_dichotomy F (star L S i) (star_le_stabilizer i) hZA hnH
      (intersection_commutator_le_center F hcommx hcommy.le hzx hzy hprod)).resolve_right hnot
  have hQy : Q F y ≤ star L S (!i) :=
    (le_sup_right.trans hRy.ge).trans (map_subtype_le _)
  have hQm : Q F m ≤ star L S (!i) :=
    (le_sup_left.trans hRy.ge).trans (map_subtype_le _)
  obtain ⟨hv,hvOriginal⟩ := source_span_commutator_of_intersection h (star L S (!i))
    (star_le_stabilizer (!i)) hadj.symm
    (fun z hz => star_locally_transitive h (!i) hadj.symm hz) hQy hQm hcommy he
  have hcore : (Q F m).map (G₀ L S).subtype =
      (parabolic L S (if i then 1 else 0)).pCoreIn 2 := by
    rw [← star_core h i, ← Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 _ (G₀ L S).subtype_injective]
    change (((starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S)).map
      (G₀ L S).subtype).pCoreIn 2 = _
    rw [map_subgroupOf_eq_of_le (star_le_completion _)]
    exact h.starredParabolic_same_core _
  refine ⟨hprod, he, ?_, hv, ?_⟩
  · have hh := congrArg (Subgroup.map (G₀ L S).subtype) he
    rwa [map_commutator, hcore] at hh
  · have hstar : (star L S (!i)).map (G₀ L S).subtype =
        starredParabolic L S (if !i then 1 else 0) :=
      map_subgroupOf_eq_of_le (star_le_completion _)
    rwa [hstar] at hvOriginal

/-- The critical seed covers the order-two Sylow in the actual D10 quotient. -/
theorem source_dihedral_first_index_and_seed_product
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* DihedralGroup 5)
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    let m := base F (!i)
    let y := base F i
    let Vx := V F x 1
    (Vx ⊓ Q F y).relIndex Vx = 2 ∧
      Q F m = Vx ⊔ (Q F y ⊓ Q F m) ∧
      Q F m = (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m) := by
  let F := reducedFamily L S
  let A := star L S i
  let m := base F (!i)
  let y := base F i
  let Vx := V F x 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hSyl := reduced_kernel_sylow h
  have hVm : Vx ≤ Q F m := V_le_neighbor_Q F (reduced_triple h).generate hZ hSyl hb hxm
  have hVx : Vx ≤ Q F x := V_le_Q F (reduced_triple h).generate hZ hSyl hb x
  have hQA : Q F m ≤ A := (le_sup_left.trans hR.ge).trans (map_subtype_le _)
  have hVA : Vx ≤ A := hVm.trans hQA
  let q := ((originalQuotient h i).symm.trans e).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 A))
  let B := (Vx.subgroupOf A).map q
  have hk : q.ker = (Q F y).subgroupOf A := by
    have hq : q.ker = pCore 2 A := by
      ext v
      change e ((originalQuotient h i).symm (QuotientGroup.mk' (pCore 2 A) v)) = 1 ↔ v ∈ pCore 2 A
      rw [map_eq_one_iff _ e.injective, map_eq_one_iff _ (originalQuotient h i).symm.injective]
      exact QuotientGroup.eq_one_iff v
    rw [hq, ← star_core h i]
    exact (comap_map_eq_self_of_injective A.subtype_injective (pCore 2 A)).symm
  have hBne : B ≠ ⊥ := by
    intro he
    have hh := (map_eq_bot_iff (Vx.subgroupOf A)).mp he
    rw [hk] at hh
    have hescape : ¬ Vx ≤ Q F y := by
      intro he
      have hseed : Z F a ≤ Vx :=
        le_iSup_of_le _ (le_iSup_of_le ((mem_ball_one F _ _).mpr (Or.inl hxa)) le_rfl)
      exact hc.2 (hseed.trans (he.trans (source_Z_Q_U (reduced_triple h) y).2))
    exact hescape (fun v hv => hh (show (⟨v,hVA hv⟩ : A) ∈ Vx.subgroupOf A from hv))
  obtain ⟨P,hP,_,_⟩ := source_common_sylow_core_index h i e R hR
  have hp : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity, DihedralGroup.nat_card]
    rw [Nat.factorization_mul (by decide) (by decide),
      Nat.prime_two.factorization, Nat.prime_five.factorization]
    norm_num
  have hBP : B ≤ (P : Subgroup (DihedralGroup 5)) :=
    (map_mono (subgroupOf_mono A hVm)).trans hP.le
  have hbcard : Nat.card B = 2 := by
    have hd := card_dvd_of_le hBP
    rw [hp] at hd
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (fun he => hBne (card_eq_one.mp he))
  have him : B = (P : Subgroup (DihedralGroup 5)) :=
    eq_of_le_of_card_ge hBP (by rw [hp,hbcard])
  have hprod : Q F m = Vx ⊔ (Q F y ⊓ Q F m) :=
    core_product_of_quotient_image A (Q F m) (Q F y) Vx q hQA hVm hk
      (hP.le.trans him.ge)
  refine ⟨?_,hprod,?_⟩
  · rw [inf_relIndex_left, ← relIndex_subgroupOf hVA, ← hk, relIndex_ker]
    exact hbcard
  · exact le_antisymm (hprod.le.trans
      (sup_le ((le_inf hVx hVm).trans le_sup_left) le_sup_right))
      (sup_le inf_le_right inf_le_right)

/-- The critical seed product contradicts noncentrality, excluding the original D10 neighbor. -/
theorem source_dihedral_neighbor_excluded
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (eD : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* DihedralGroup 5)
    (hfield : Nat.card k = 2)
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i)) :
    False := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hQU := fun v => (source_Z_Q_U (reduced_triple h) v).2
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hnot := source_dihedral_intersection_not_central h i hb hxadj hne T R hT hR e
    hz hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor eD hfield Ry hRy hc hxa
  have hgen : star L S i = (Q F x ⊔ Q F y) ⊔ Q F m := by
    have hh := star_three_core_generation h i hxadj hne T R hT hR
    simpa only [sup_comm,sup_left_comm,sup_assoc] using hh
  have hproducts := source_dihedral_first_index_and_seed_product h (!i) hb hc hxa
    (by simpa only [Bool.not_not] using hxadj.symm) eD Ry
    (by simpa only [Bool.not_not] using hRy)
  have hseed : (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m) =
      V F x 1 ⊔ (Q F m ⊓ Q F y) := by
    calc
      _ = Q F m := by simpa only [Bool.not_not] using hproducts.2.2.symm
      _ = V F x 1 ⊔ (Q F y ⊓ Q F m) := by simpa only [Bool.not_not] using hproducts.2.1
      _ = _ := by rw [inf_comm]
  have hylt : ¬ Z F m ≤ Z F y := by
    intro hle
    let : Finite (Z F y) := Finite.of_injective
      (inclusion (Z_le_stabilizer F y)) (inclusion_injective _)
    have hlecard := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _)
    change Nat.card (Z F m) ≤ Nat.card (Z F y) at hlecard
    rw [hcard,hcardy] at hlecard
    have hq : 1 < Nat.card k := Finite.one_lt_card
    nlinarith
  apply hnot
  exact seed_alternative_centralizes_intersection F hQU hZ hxadj.symm hadj.symm
    (star L S i) (star_le_stabilizer i) hgen hz
    (V_le_neighbor_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb hxadj.symm)
    (V_elementary F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x)
    hcommx hcommy hzx hzy hylt hmin hseed

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
