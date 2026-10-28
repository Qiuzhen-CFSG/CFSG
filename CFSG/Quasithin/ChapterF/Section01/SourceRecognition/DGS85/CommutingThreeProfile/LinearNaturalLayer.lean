module
public import Theory.Representation.RankOne.QuadraticRecognition.SmallFixedSeed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearCentralIntersection
import all CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCentralExclusion

/-!
# The actual natural layer in the linear-neighbor row

The linear-neighbor product forces H = V_x ∩ V_y to centralize Q_m.
The earlier central-intersection comparison then gives H = Z_m. In the
literal quotient D = V_y/Z_y, the image C of Z_m has order q and contains
the commutator with V_x. The marked image of V_x is a full SL₂(q) Sylow.
It fixes C since Z_m ≤ V_x and V_x is elementary abelian. Local transitivity
shows that the conjugates of C generate D, and the actual critical pair
makes its action nontrivial. SmallFixedSeed therefore gives |D| = q² and
an equivariant linear equivalence with the natural module, also for q = 2.

The final formula retains the original local quotient marking and every
original actor's inclusion and conjugation on the original quotient vectors.
The first theorem isolates the central case; the second discharges that
premise using the proved linear product and center argument.

The common Sylows, natural middle-center order and minimality, conjugated
indices and equality of the field orders remain the genuine earlier inputs.
To exclude the linear row in (12.4), source assembly must still apply (8.5)
with its exact quotient V_y/C_{V_y}(O²(L_y)); that centralizer must be matched
with Z_y. No linear or binary exclusion, or later (12.9)/(13.1) classification,
is claimed by this natural-layer construction.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(8.5), (12.1), (12.3)(c), (12.4), printed pp.139,178--181.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local instance {l : Type*} [Field l] [CharP l 2] : Algebra (ZMod 2) l := ZMod.algebra l 2

/-- A central intersection forces natural coordinates with the original quotient action. -/
theorem source_linear_central_intersection_natural
    {k l : Type*} [Field k] [Finite k] [CharP k 2]
    [Field l] [Finite l] [CharP l 2]
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
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* Matrix.SpecialLinearGroup (Fin 2) l)
    (hfield : Nat.card k = Nat.card l)
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hcentral : V (reducedFamily L S) x 1 ⊓
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ≤
        centralizer (Q (reducedFamily L S) (base (reducedFamily L S) i) : Set (G₀ L S))) :
    let F := reducedFamily L S
    let y := base F (!i)
    let D := V F y 1
    let := V_elementary F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y
    let : ((Z F y).subgroupOf D).Normal := normal_of_isMulCommutative _
    Nat.card (D ⧸ (Z F y).subgroupOf D) = Nat.card l ^ 2 ∧
      ∃ E : Additive (D ⧸ (Z F y).subgroupOf D) ≃ₗ[ZMod 2] (Fin 2 → l),
        ∀ u : L (if !i then 1 else 0), ∀ d : D,
          E (Additive.ofMul (QuotientGroup.mk
            ⟨(originalActor (L := L) (S := S) (!i) u : G₀ L S) * d *
              (originalActor (L := L) (S := S) (!i) u : G₀ L S)⁻¹,
              (mem_normalizer_iff.mp (star_normalizes_span h (!i)
                (originalActor (L := L) (S := S) (!i) u).property) d).mp d.property⟩)) =
            Matrix.mulVec (eLin (QuotientGroup.mk u)).val (E (Additive.ofMul (QuotientGroup.mk d))) := by
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
  let eA := (originalQuotient h (!i)).symm.trans eLin
  let τ := ρ.comp eA.symm.toMonoidHom
  let q := eA.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  obtain ⟨_,_,_,P,hP⟩ := source_linear_first_index_and_product h (!i) hb hc hxa
    (by simpa only [Bool.not_not] using hxadj.symm)
    eLin (by cases i <;> exact e) Ry (by simpa only [Bool.not_not] using hRy)
  have hτ (u : A) : τ (q u) = ρ (QuotientGroup.mk u) := by
    change ρ (eA.symm (eA (QuotientGroup.mk u))) = _
    rw [eA.symm_apply_apply]
  have hmov : subspaceCommutator τ ⊤ (P : Subgroup _) ≤ binarySpace C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t,ht,v,_,rfl⟩
    rw [← hP] at ht
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
  have hfixed : binarySpace C ≤ fixedSpace τ (P : Subgroup _) := by
    rintro v ⟨z,hz,rfl⟩ t
    have ht := hP.ge t.property
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
  have hcardC : Nat.card (binarySpace C) = Nat.card l :=
    (binarySubgroup_card (binarySpace C)).symm.trans (hC.trans hfield)
  obtain ⟨horder,E,hE⟩ := Representation.RankOne.QuadraticRecognition.sl2_small_seed_natural
    τ P (binarySpace C) hneτ hfixed hseed hmov hcardC.le
  refine ⟨horder,E,?_⟩
  intro u d
  have hqu : q (originalActor (L := L) (S := S) (!i) u) = eLin (QuotientGroup.mk u) := by
    change eLin ((originalQuotient h (!i)).symm
      (QuotientGroup.mk (originalActor (L := L) (S := S) (!i) u))) = _
    exact congrArg eLin
      ((congrArg (originalQuotient h (!i)).symm (originalQuotient_mk h (!i) u).symm).trans
        ((originalQuotient h (!i)).symm_apply_apply (QuotientGroup.mk u)))
  apply (congrArg E (congrArg Additive.ofMul
    (hρ (originalActor (L := L) (S := S) (!i) u) d))).symm.trans
  have he := hE (q (originalActor (L := L) (S := S) (!i) u)) (Additive.ofMul (π d))
  rw [hτ] at he
  exact he.trans (congrArg (fun z : SL(2,l) =>
    Matrix.mulVec z.val (E (Additive.ofMul (π d)))) hqu)

/-- The linear row itself forces a natural quotient, including SL₂(2).
The middle-core centralization is proved, not retained as a premise. -/
theorem source_linear_intersection_natural
    {k l : Type*} [Field k] [Finite k] [CharP k 2]
    [Field l] [Finite l] [CharP l 2]
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
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* Matrix.SpecialLinearGroup (Fin 2) l)
    (hfield : Nat.card k = Nat.card l)
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i)) :
    let F := reducedFamily L S
    let y := base F (!i)
    let D := V F y 1
    let := V_elementary F (reduced_triple h).generate
      (fun v => (source_Z_Q_U (reduced_triple h) v).1) (reduced_kernel_sylow h) hb y
    let : ((Z F y).subgroupOf D).Normal := normal_of_isMulCommutative _
    Nat.card (D ⧸ (Z F y).subgroupOf D) = Nat.card l ^ 2 ∧
      ∃ E : Additive (D ⧸ (Z F y).subgroupOf D) ≃ₗ[ZMod 2] (Fin 2 → l),
        ∀ u : L (if !i then 1 else 0), ∀ d : D,
          E (Additive.ofMul (QuotientGroup.mk
            ⟨(originalActor (L := L) (S := S) (!i) u : G₀ L S) * d *
              (originalActor (L := L) (S := S) (!i) u : G₀ L S)⁻¹,
              (mem_normalizer_iff.mp (star_normalizes_span h (!i)
                (originalActor (L := L) (S := S) (!i) u).property) d).mp d.property⟩)) =
            Matrix.mulVec (eLin (QuotientGroup.mk u)).val (E (Additive.ofMul (QuotientGroup.mk d))) := by
  have hcentral : V (reducedFamily L S) x 1 ⊓
      V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ≤
        centralizer (Q (reducedFamily L S) (base (reducedFamily L S) i) : Set (G₀ L S)) := by
    cases i
    · exact (source_linear_intersection_centralizes h true hb hc hxa hxadj.symm
        eLin e Ry hRy T R hT hR hzx hzy hcommx hcommy hmin hz hcard hcardy).1
    · exact (source_linear_intersection_centralizes h false hb hc hxa hxadj.symm
        eLin e Ry hRy T R hT hR hzx hzy hcommx hcommy hmin hz hcard hcardy).1
  exact source_linear_central_intersection_natural h i hb hxadj hne T R hT hR e hz
    hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor eLin hfield Ry hRy hc hxa hcentral

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
