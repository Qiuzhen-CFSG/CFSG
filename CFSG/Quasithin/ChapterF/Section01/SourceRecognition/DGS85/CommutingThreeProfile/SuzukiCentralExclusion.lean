module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CentralIntersectionLayer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiIndices
public import Theory.Representation.RankOne.QuadraticRecognition.SuzukiActors
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.ConjugationImage

/-!
# Excluding the central intersection for nonbinary Suzuki neighbors

In the central alternative on DGS p.180, the existing center comparison
identifies H = V_x ∩ V_y with Z_m. Its image on the actual quotient V_y/Z_y
has order q and contains the commutator with V_x. The original Suzuki
marking identifies the image of V_x with a full Sylow omega-center of order q.

For a nontrivial Suzuki action, apply the proved square bound to its dual:
the moved space of this omega-center has order at least q². This contradicts
the order-q bound. The action is nontrivial by the critical geometry itself:
a trivial action would make Z_m invariant at y, then local transitivity
would give V_y = Z_m = V_x and put the critical Z_a inside U_y.

This proves the central-case exclusion for the nonbinary Suzuki branch
without the separate Chapter 8 nonnatural-module input. Earlier common
Sylows, natural-center orders, field compatibility, and conjugated index
bounds remain explicit. The middle-core product is a separate obligation;
no assertion of DGS (12.9) or (13.1) is made here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
Part II, (12.1), (12.3)(a--c), printed pp.178--180. The dual square bound
is the existing Suzuki specialization of the module theory on pp.109--114.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups BenderSuzuki.Converse
open scoped IsMulCommutative

private theorem small_moved_trivial {n : ℕ} (hn : 0 < n)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup n) W)
    (T : Sylow 2 (SuzukiMatrixGroup n))
    (hsmall : Nat.card (subspaceCommutator ρ ⊤ (omegaOneAmbient (T : Subgroup _))) ≤
      2 ^ (2 * n + 1)) : ρ = 1 := by
  by_contra hne
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 n hn).1
  have hf : Function.Injective ρ := ρ.ker_eq_bot_iff.mp
    (ρ.normal_ker.eq_bot_or_eq_top.resolve_right
      (fun hk => hne (MonoidHom.ker_eq_top_iff.mp hk)))
  let E := omegaOneAmbient (T : Subgroup (SuzukiMatrixGroup n))
  let : IsElementaryAbelian 2 E := suzukiSylow_omega_elementary hn (MulEquiv.refl _) T
  have hcard : Nat.card E = 2 ^ (2 * n + 1) := suzukiSylow_omega_card hn (MulEquiv.refl _) T
  have hbig : 2 < Nat.card E := by
    rw [hcard]
    exact (show 2 = (2:ℕ)^1 by norm_num).trans_lt
      (Nat.pow_lt_pow_right (by decide) (by omega))
  let : Finite (Module.Dual (ZMod 2) W) := Finite.of_injective
    (fun f : Module.Dual (ZMod 2) W => (f : W → ZMod 2)) DFunLike.coe_injective
  have hs := Representation.RankOne.QuadraticRecognition.suzuki_noncyclic_square_bound hn
    ρ.dual (faithful_dual ρ hf) T E (omegaOneAmbient_le _) hbig
  have he : Nat.card (Module.Dual (ZMod 2) W ⧸ fixedSpace ρ.dual E) =
      Nat.card (subspaceCommutator ρ ⊤ E) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) W ⧸ fixedSpace ρ.dual E),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := subspaceCommutator ρ ⊤ E)]
    exact congrArg (fun d => Nat.card (ZMod 2) ^ d)
      (fixedCodim_dual_eq_moved_finrank ρ E)
  rw [he, hcard] at hs
  have hp : 1 < 2 ^ (2 * n + 1) := one_lt_pow₀ (by decide) (by omega)
  nlinarith

namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

private theorem center_layer_action_nontrivial
    (F : Bool → Subgroup G) [∀ i, Finite (F i)]
    (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hSyl : ∀ v, ∃ T : Sylow 2 (U F v),
      (T : Subgroup (U F v)).map (U F v).subtype = Q F v)
    (hb : 2 < b F) {a x y m : Vertex F}
    (hc : IsCriticalPair F a y)
    (hxa : (graph F).Adj x a) (hym : (graph F).Adj y m)
    (A : Subgroup G) (hA : A ≤ stabilizer F y)
    (htrans : ∀ z, (graph F).Adj y z → ∃ g ∈ A, g • m = z)
    (g : G) (hgm : g • m = m) (hgy : g • y = x)
    (hzy : Z F y ≤ Z F m) :
    let := V_elementary F hgen hZ hSyl hb y
    let : ((Z F y).subgroupOf (V F y 1)).Normal := normal_of_isMulCommutative _
    ∀ ρ : Representation (ZMod 2) (A ⧸ pCore 2 A)
      (Additive (V F y 1 ⧸ (Z F y).subgroupOf (V F y 1))),
      (∀ t : A, ∀ d : V F y 1,
        (ρ (QuotientGroup.mk t) (Additive.ofMul (QuotientGroup.mk d))).toMul =
          QuotientGroup.mk ⟨(t : G) * d * (t : G)⁻¹,
            (mem_normalizer_iff.mp (stabilizer_normalizes_V F y 1 (hA t.property)) d).mp d.property⟩) →
      ρ ≠ 1 := by
  let D := V F y 1
  let := V_elementary F hgen hZ hSyl hb y
  let : ((Z F y).subgroupOf D).Normal := normal_of_isMulCommutative _
  dsimp only
  intro ρ hρ htriv
  have hZD : Z F m ≤ D :=
    le_iSup_of_le m (le_iSup_of_le ((mem_ball_one F y m).mpr (Or.inl hym)) le_rfl)
  have hn : A ≤ normalizer (Z F m : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht d hd
    let tA : A := ⟨t,ht⟩
    let dD : D := ⟨d,hZD hd⟩
    let cD : D := ⟨t * d * t⁻¹,
      (mem_normalizer_iff.mp (stabilizer_normalizes_V F y 1 (hA ht)) d).mp (hZD hd)⟩
    have he : (QuotientGroup.mk cD : D ⧸ (Z F y).subgroupOf D) = QuotientGroup.mk dD := by
      have hh := hρ tA dD
      rw [htriv] at hh
      exact hh.symm
    have hcd : cD * dD⁻¹ ∈ (Z F y).subgroupOf D := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' ((Z F y).subgroupOf D)) (cD * dD⁻¹) = 1
      rw [map_mul, map_inv]
      change QuotientGroup.mk cD * (QuotientGroup.mk dD)⁻¹ = 1
      rw [he, mul_inv_cancel]
    have hh := (Z F m).mul_mem (hzy hcd) hd
    change (t * d * t⁻¹ * d⁻¹) * d ∈ Z F m at hh
    simpa only [inv_mul_cancel_right] using hh
  have hD : D = Z F m := by
    apply le_antisymm _ hZD
    change V F y 1 ≤ Z F m
    rw [V_eq_center_sup_neighbor_conjugates F A hA hym htrans]
    exact sup_le hzy (conjugateSpanBy_le le_rfl hn)
  have hX : V F x 1 = Z F m := by
    rw [← hgy, V_translate, show V F y 1 = Z F m from hD, ← Z_translate, hgm]
  have hseed : Z F a ≤ V F x 1 :=
    le_iSup_of_le a (le_iSup_of_le ((mem_ball_one F x a).mpr (Or.inl hxa)) le_rfl)
  have hV : D ≤ Q F y := V_le_Q F hgen hZ hSyl hb y
  have hQU : Q F y ≤ U F y := by
    obtain ⟨T,hT⟩ := hSyl y
    rw [← hT]
    exact map_subtype_le _
  exact hc.2 (hseed.trans (hX.le.trans (hD.ge.trans (hV.trans hQU))))
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile

namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The actual critical configuration excludes the central intersection in the
nonbinary Suzuki branch, with its original/starred quotient marking. -/
theorem source_suzuki_intersection_not_central
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
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
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
  let eA := (originalQuotient h (!i)).symm.trans eSuz
  let τ := ρ.comp eA.symm.toMonoidHom
  let q := eA.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  obtain ⟨_,_,P,hP⟩ := source_suzuki_first_index (k := k) h (!i) hb hc hxa hxadj.symm hadj.symm
    hn eSuz (by cases i <;> exact e) Ry hRy
  have hmov : subspaceCommutator τ ⊤ (omegaOneAmbient (P : Subgroup _)) ≤ binarySpace C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t,ht,v,_,rfl⟩
    rw [← hP] at ht
    obtain ⟨u,hu,rfl⟩ := ht
    obtain ⟨d,hd⟩ := QuotientGroup.mk'_surjective ((Z F y).subgroupOf D) v.toMul
    have hv : v = Additive.ofMul (π d) := (congrArg Additive.ofMul hd).symm
    rw [hv]
    change (τ (q u) (Additive.ofMul (π d))).toMul / (π d) ∈ C
    rw [div_eq_mul_inv]
    have hτ : τ (q u) = ρ (QuotientGroup.mk u) := by
      change ρ (eA.symm (eA (QuotientGroup.mk u))) = _
      rw [eA.symm_apply_apply]
    rw [hτ]
    change (ρ (QuotientGroup.mk u) (Additive.ofMul (QuotientGroup.mk d))).toMul * (π d)⁻¹ ∈ C
    rw [hρ u d]
    change π _ * (π d)⁻¹ ∈ C
    rw [← map_inv, ← map_mul]
    apply hbound
    apply mem_map_of_mem
    change (u : G₀ L S) * d * (u : G₀ L S)⁻¹ * (d : G₀ L S)⁻¹ ∈ ⁅V F x 1,D⁆
    exact commutator_mem_commutator hu d.property
  have hcardC : Nat.card (binarySpace C) = 2 ^ (2 * n + 1) :=
    (binarySubgroup_card (binarySpace C)).symm.trans (hC.trans hfield)
  have hτ := small_moved_trivial hn τ P
    ((Nat.card_le_card_of_injective (Submodule.inclusion hmov)
      (Submodule.inclusion_injective hmov)).trans_eq hcardC)
  apply hρne
  apply MonoidHom.ext
  intro z
  apply LinearMap.ext
  intro v
  have he := DFunLike.congr_fun (DFunLike.congr_fun hτ (eA z)) v
  change ρ (eA.symm (eA z)) v = v at he
  change ρ z v = v
  exact (by simpa only [eA.symm_apply_apply] using he)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
