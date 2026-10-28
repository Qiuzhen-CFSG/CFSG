module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCenterPair
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiSecondKernelUpper
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiFaithfulCenterLayer
public import Theory.GroupAction.IrreducibleQuotientMovement
public import Theory.GroupTheory.Commutator.ReciprocalMovement

/-!
# The fixed-center quotient from the actual Suzuki geometry

The two critical centers generate the starred endpoint modulo its core.
Its previously proved irreducible second-kernel section is fully generated
by commutators. Reciprocal three-subgroups rotation therefore identifies
the common centralizer of the two centers in V with C_V(star). The geometric
pair bound gives [V:C_V(star)] ≤ q⁴ in the reduced and original groups.

Construct conjugation on this literal elementary quotient and descend it
through the intrinsic core. The central-section kernel argument gives
faithfulness, so Suzuki minimum degree makes the bound sharp and the
original action irreducible. The representative formula uses the original
local inclusion and quotient map throughout.

This is the Z = C_V(tilde L) step in DGS85 (12.6), printed p.183, for
q > 2. Identifying this fixed subgroup with the geometric Z_beta remains
necessary. The input Suzuki/linear markings, common parameter, common
Sylows, natural neighboring center and earlier commutator identities are
retained source premises. Neither full second-kernel containment nor
(12.5) selection or the remaining (12.6)--(12.9)/(13.1) conclusions are
asserted here.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1), (12.3), (12.5)--(12.6), printed pp.178--183.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The whole starred endpoint has fixed index at most q⁴ in the actual center span. -/
theorem source_suzuki_center_fixed_upper
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n) (hq : Nat.card k = 2^(2*n+1))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,k))
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    (T₀ : Sylow 2 (star L S (!i)))
    (hT₀ : (T₀ : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hnat : Noncommuting.HasNaturalCenter (star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))))
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) i) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1, star L S i⁆) :
    let F := reducedFamily L S
    let V₀ := V F (base F i) 1
    (centralizer (star L S i : Set (G₀ L S))).relIndex V₀ ≤ (2^(2*n+1))^4 ∧
      (centralizer ((star L S i).map (G₀ L S).subtype : Set G)).relIndex
        (V₀.map (G₀ L S).subtype) ≤ (2^(2*n+1))^4 := by
  let F := reducedFamily L S
  let v := base F i
  let A := star L S i
  let D := Q F v
  let N := ballKernel F v 2
  let V₀ := V F v 1
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hplace : D ≤ star L S (!i) :=
    (le_sup_left.trans hT₀.ge).trans (map_subtype_le _)
  let : (N.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
  let := source_second_kernel_elementary h i hplace hnat hcomm.le
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 n hn).1
  let : Nontrivial (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) :=
    eSuz.surjective.nontrivial
  obtain ⟨ρ,hf,hirr,_,hρ⟩ := source_suzuki_second_kernel_layer h i hb hc hxa hxm hn hq
    eSuz eLin T hT R hR hzy hcomm T₀ hT₀ hnat hfull
  have hAD : A ≤ normalizer (D : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (CommutingTrivial.stabilizer_normalizes_Q F v)
  have hAN : A ≤ normalizer (N : Set (G₀ L S)) :=
    (star_le_stabilizer i).trans (stabilizer_le_normalizer_ballKernel F v 2)
  let actor : L (if i then 1 else 0) →* A :=
    ((subgroupOfEquivOfLe (star_le_completion _)).symm.toMonoidHom).comp
      (inclusion (local_le_starredParabolic _))
  have hm : D ≤ ⁅D,A⁆ ⊔ (D ⊓ N) :=
    le_commutator_sup_of_irreducible_quotient A D N hAD actor (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) ρ hf hirr hρ
  have hDD : ⁅D,D⁆ ≤ N := by
    have hd : _root_.commutator D ≤ N.subgroupOf D :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N.subgroupOf D)).mp
        inferInstance
    have hh := map_mono (f := D.subtype) hd
    rw [map_subtype_commutator,subgroupOf_map_subtype] at hh
    exact hh.trans inf_le_left
  obtain ⟨g,hg,hgen,hbound,_⟩ := source_suzuki_center_pair h i hb hc hxa hxm hn hq
    eSuz eLin T hT R hR
  have he := centralizer_seed_eq_of_reciprocal_movement A (Z F a ⊔ Z F (g • a)) D V₀ N
    (Z F v) hgen hAD hAN hDD
    ((source_core_span_centralizer_eq_second_kernel h i hplace hnat).ge.trans inf_le_right)
    hcomm.le (source_center_centralizes_star_of_neighbor_inclusion h i hzy R hR) hm
  have hbnd : (centralizer (A : Set (G₀ L S))).relIndex V₀ ≤ (2^(2*n+1))^4 := by
    rw [←inf_relIndex_left,←he,inf_relIndex_left]
    exact hbound
  refine ⟨hbnd,?_⟩
  rw [←inf_relIndex_left,map_inf_centralizer_of_injective _ (G₀ L S).subtype_injective,
    relIndex_map_map_of_injective _ _ (G₀ L S).subtype_injective,inf_relIndex_left]
  exact hbnd

/-- Construct the faithful irreducible original action of order q⁴ modulo its actual fixed subgroup. -/
theorem source_suzuki_fixed_center_layer
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S))
    {a x : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) i))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hxm : (graph (reducedFamily L S)).Adj x (base (reducedFamily L S) (!i)))
    {n : ℕ} (hn : 0 < n) (hq : Nat.card k = 2^(2*n+1))
    (eSuz : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      SuzukiMatrixGroup n)
    (eLin : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃*
      SL(2,k))
    (T : Sylow 2 (star L S (!i)))
    (hT : (T : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (star L S i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    (T₀ : Sylow 2 (star L S (!i)))
    (hT₀ : (T₀ : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hnat : Noncommuting.HasNaturalCenter (star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))))
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) i) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1, star L S i⁆) :
    let F := reducedFamily L S
    let v := base F i
    let V₀ := V F v 1
    let C := V₀ ⊓ centralizer (star L S i : Set (G₀ L S))
    let := V_elementary F (reduced_triple h).generate
      (fun w => (source_Z_Q_U (reduced_triple h) w).1) (reduced_kernel_sylow h) hb v
    let : (C.subgroupOf V₀).Normal := normal_of_isMulCommutative _
    ∃ ρ : Representation (ZMod 2)
      (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0)))
      (Additive (V₀ ⧸ C.subgroupOf V₀)),
      Function.Injective ρ ∧ ρ.IsIrreducible ∧
      Nat.card (V₀ ⧸ C.subgroupOf V₀) = (2^(2*n+1))^4 ∧
      ∀ a : L (if i then 1 else 0), ∀ x : V₀,
        (ρ (QuotientGroup.mk a) (Additive.ofMul (QuotientGroup.mk x))).toMul =
          QuotientGroup.mk ⟨(originalActor (L := L) (S := S) i a : G₀ L S) * x *
            (originalActor (L := L) (S := S) i a : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp (star_normalizes_span h i
              (originalActor (L := L) (S := S) i a).property) x).mp x.property⟩ := by
  let F := reducedFamily L S
  let v := base F i
  let A := star L S i
  let V₀ := V F v 1
  let C := V₀ ⊓ centralizer (A : Set (G₀ L S))
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun w => (source_Z_Q_U (reduced_triple h) w).1
  let := V_elementary F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb v
  let : (C.subgroupOf V₀).Normal := normal_of_isMulCommutative _
  let : Finite V₀ := Finite.of_injective
    (inclusion ((V_le_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb v).trans
      (Q_le_stabilizer F v))) (inclusion_injective _)
  have hAV := star_normalizes_span h i
  have hAC : A ≤ centralizer (C : Set (G₀ L S)) :=
    le_centralizer_iff.mp inf_le_right
  have hZC : Z F v ≤ C := le_inf (Z_le_V F v 1)
    (source_center_centralizes_star_of_neighbor_inclusion h i hzy R hR)
  obtain ⟨α,hα⟩ := exists_quotient_conjugation_action A V₀ C hAV
    (hAC.trans (Subgroup.centralizer_le_normalizer _)) inferInstance
  have hkill := quotient_conjugation_action_kills_commutator_layer A V₀ C (Q F v)
    inferInstance hAV (hcomm.le.trans hZC) α hα
  have hk : pCore 2 A ≤ α.ker := by
    intro a ha
    apply hkill
    rw [←star_core h i]
    exact mem_map_of_mem A.subtype ha
  let β := QuotientGroup.lift (pCore 2 A) α hk
  let : MulDistribMulAction (A ⧸ pCore 2 A) (V₀ ⧸ C.subgroupOf V₀) :=
    MulDistribMulAction.compHom _ β
  let σ : Representation (ZMod 2) (A ⧸ pCore 2 A) (Additive (V₀ ⧸ C.subgroupOf V₀)) :=
    Representation.ofElementaryAbelianAction
  have hσ : ∀ a : A, ∀ x : V₀,
      (σ (QuotientGroup.mk a) (Additive.ofMul (QuotientGroup.mk x))).toMul =
        QuotientGroup.mk ⟨(a : G₀ L S) * x * (a : G₀ L S)⁻¹,
          (mem_normalizer_iff.mp (hAV a.property) x).mp x.property⟩ := hα
  have hf : Function.Injective σ := central_quotient_conjugation_faithful A V₀ C hAV hAC
    (source_suzuki_span_centralizer_le_core h i eSuz) σ hσ
  let ρ := σ.comp (originalQuotient h i).toMonoidHom
  have hfaith : Function.Injective ρ := hf.comp (originalQuotient h i).injective
  have hsmall : Nat.card (V₀ ⧸ C.subgroupOf V₀) ≤ (2^(2*n+1))^4 := by
    change C.relIndex V₀ ≤ _
    rw [inf_relIndex_left]
    exact (source_suzuki_center_fixed_upper h i hb hc hxa hxm hn hq eSuz eLin T hT R hR
      hzy hcomm T₀ hT₀ hnat hfull).1
  obtain ⟨hirr,hcard⟩ := Representation.Suzuki.irreducible_of_faithful_small_card
    (ρ.comp eSuz.symm.toMonoidHom) (hfaith.comp eSuz.symm.injective) hsmall
  refine ⟨ρ,hfaith,(Representation.irreducible_comp_surjective_iff
    eSuz.symm.toMonoidHom eSuz.symm.surjective ρ).mp hirr,hcard,?_⟩
  intro a x
  exact hσ (originalActor (L := L) (S := S) i a) x

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
