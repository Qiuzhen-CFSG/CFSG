module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryThreeParabolic
public import Theory.Representation.BinaryOffender.ComponentSum
public import Theory.SpecificGroups.PSL3Two.Automorphisms.SylowStabilizer

/-!
# The marked binary-three action on the original quotient

The single transvection factor supplies its canonical moved subspace. Its
order distinguishes the natural GL3(2) model from the other G.6.4 models.
Every compatible automorphism is inner on this space. A two-kernel lift
then fixes each subgroup above the specified Sylow, whose model is
self-normalizing. The ambient application retains the literal conjugation
on W/Z_S and the same invariant cover.

Source: Aschbacher–Smith 6.1.19, printed p.675, using G.6.4(2a), p.345.
The cubic rotation and final Sylow invariance are assembled in ThreeAction;
S5 escape and the amalgam contradiction remain with the natural owner.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open CFSG.Quasithin.ChapterG.Section06
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction

private theorem linear_card (n : ℕ) :
    Nat.card (BinaryLinear.OuterCyclic.LinearGroup n) =
      ∏ i : Fin n, (2^n - 2^i.val) := by
  rw [←Nat.card_congr (BinaryLinear.OuterCyclic.matrixEquivLinear n).toEquiv,
    Matrix.card_GL_field]
  simp

private theorem model_three {A V : Type*} [Group A] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) A V)
    (K : Subgroup A) (U : Submodule (ZMod 2) V)
    (hcard : Nat.card K = 168) (hm : FactorModel ρ K U) :
    HasModelOn ρ K U (binaryLinearAction 3) := by
  rcases hm with ⟨n,hlo,hhi,hm⟩ | ⟨n,hlo,hhi,hm⟩ | ⟨n,hn,hm⟩
  · have hc : Nat.card (BinaryLinear.OuterCyclic.LinearGroup n) = 168 := by
      obtain ⟨e,_,_⟩ := hm
      exact (Nat.card_congr e.toEquiv).symm.trans hcard
    have hn : n = 3 := by
      rw [linear_card] at hc
      interval_cases n <;> norm_num [Fin.prod_univ_succ] at hc
      rfl
    exact hn ▸ hm
  · obtain ⟨e,_,_⟩ := hm
    have hc := (Nat.card_congr e.toEquiv).symm.trans hcard
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] at hc
    interval_cases n <;> norm_num at hc
  · obtain ⟨e,_,_⟩ := hm
    have hc := (Nat.card_congr e.toEquiv).symm.trans hcard
    rw [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] at hc
    rcases hn with rfl | rfl <;> norm_num at hc

universe u
variable {A V : Type u} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) A V}

theorem canonical_model (d : SmallTransvectionProductModel ρ)
    (hs : d.factors = {⊤}) (hc : Nat.card A = 168) :
    HasModelOn ρ ⊤ (subspaceCommutator ρ ⊤ ⊤) (binaryLinearAction 3) := by
  have htop : (⊤ : Subgroup A) ∈ d.factors := by rw [hs]; simp
  obtain ⟨t,_,he,⟨dt⟩⟩ := d.marked ⊤ htop
  have hU : dt.space.toSubmodule = subspaceCommutator ρ ⊤ ⊤ := by
    rw [dt.space_eq,←commutator_conjugateSpanBy_zpowers,conjugateSpanBy_zpowers_top,←he]
  have hm := model_three ρ (normalClosure ({t} : Set A)) dt.space.toSubmodule
    (by rw [←he,Nat.card_congr Subgroup.topEquiv.toEquiv]; exact hc) dt.model
  rwa [←he,hU] at hm

private theorem moved_map_le (α : MulAut A) (β : V ≃ₗ[ZMod 2] V)
    (hβ : ∀ a v, β (ρ a v) = ρ (α a) (β v)) :
    (subspaceCommutator ρ ⊤ ⊤).map β.toLinearMap ≤ subspaceCommutator ρ ⊤ ⊤ := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨a,_,v,_,rfl⟩
  change β (ρ a v-v) ∈ subspaceCommutator ρ ⊤ ⊤
  rw [map_sub,hβ]
  exact Submodule.subset_span ⟨α a,mem_top _,β v,Submodule.mem_top,rfl⟩

theorem compatible_inner
    (hm : HasModelOn ρ ⊤ (subspaceCommutator ρ ⊤ ⊤) (binaryLinearAction 3))
    (α : MulAut A) (β : V ≃ₗ[ZMod 2] V)
    (hβ : ∀ a v, β (ρ a v) = ρ (α a) (β v)) :
    ∃ a : A, α = MulAut.conj a := by
  let U := subspaceCommutator ρ ⊤ ⊤
  have hback : U.map β.symm.toLinearMap ≤ U := moved_map_le α.symm β.symm (by
    intro a v
    apply β.injective
    rw [β.apply_symm_apply,hβ,α.apply_symm_apply,β.apply_symm_apply])
  have hU : U.map β.toLinearMap = U := by
    refine le_antisymm (moved_map_le α β hβ) ?_
    intro v hv
    exact ⟨β.symm v,hback ⟨v,hv,rfl⟩,β.apply_symm_apply v⟩
  let b := β.ofSubmodules U U hU
  obtain ⟨j,f,hstable,hmodel⟩ := hm
  let e : A ≃* BinaryLinear.OuterCyclic.LinearGroup 3 := Subgroup.topEquiv.symm.trans j
  let g : BinaryLinear.OuterCyclic.LinearGroup 3 := (f.symm.trans b).trans f
  let a := e.symm g
  have hmodel' (x : A) (v : U) :
      f ⟨ρ x v,hstable ⟨x,mem_top x⟩ v⟩ = e x (f v) := hmodel ⟨x,mem_top x⟩ v
  have hcov (x : A) : e (α x) * g = g * e x := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨w,rfl⟩ := f.surjective v
    change e (α x) (f (b (f.symm (f w)))) = f (b (f.symm (e x (f w))))
    rw [f.symm_apply_apply]
    rw [←hmodel' x w,f.symm_apply_apply,←hmodel' (α x) (b w)]
    apply congrArg f
    apply Subtype.ext
    exact (hβ x w).symm
  refine ⟨a,?_⟩
  ext x
  apply e.injective
  change e (α x) = e (a*x*a⁻¹)
  rw [map_mul,map_mul,map_inv,show e a = g from e.apply_symm_apply g]
  exact (eq_mul_inv_iff_mul_eq).mpr (hcov x)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction
variable {A D : Type*} [Group A] [Finite A] [Group D]

private theorem self_normalizing_sylow (S : Sylow 2 A)
    (f : A →* D) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (e : D ≃* BinaryLinear.OuterCyclic.LinearGroup 3) :
    normalizer (S : Set A) = (S : Subgroup A) := by
  let q := (e.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm).toMonoidHom.comp f
  have hq : Function.Surjective q :=
    (e.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm).surjective.comp hf
  have hker : q.ker = f.ker := MonoidHom.ker_comp_of_injective _ _
    (e.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm).injective
  have hkS : q.ker ≤ (S : Subgroup A) := hker ▸ hk.le_sylow_of_normal S
  have hm := Matrix.PSL3Two.self_normalizing_sylow (S.mapSurjective hq)
  change normalizer (((S : Subgroup A).map q) : Set Matrix.PSL3Two.SL) =
    (S : Subgroup A).map q at hm
  apply le_antisymm ?_ (S : Subgroup A).le_normalizer
  intro x hx
  have hqx : q x ∈ normalizer (((S : Subgroup A).map q) : Set Matrix.PSL3Two.SL) :=
    (S : Subgroup A).le_normalizer_map q (mem_map_of_mem q hx)
  rw [hm] at hqx
  have hh : x ∈ ((S : Subgroup A).map q).comap q := hqx
  rwa [comap_map_eq_self hkS] at hh

theorem covariant_normalizes_overgroup (S : Sylow 2 A)
    (f : A →* D) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (e : D ≃* BinaryLinear.OuterCyclic.LinearGroup 3)
    (α : MulAut A) (hS : (S : Subgroup A).map α.toMonoidHom = S)
    (a : A) (ha : ∀ x, f (α x) = f (a*x*a⁻¹))
    (B : Subgroup A) (hSB : (S : Subgroup A) ≤ B) :
    B.map α.toMonoidHom = B := by
  have hkerS : f.ker ≤ (S : Subgroup A) := hk.le_sylow_of_normal S
  have hkerB : f.ker ≤ B := hkerS.trans hSB
  have hmem (U : Subgroup A) (hker : f.ker ≤ U) (x : A) :
      α x ∈ U ↔ a*x*a⁻¹ ∈ U := by
    rw [←comap_map_eq_self hker]
    change f (α x) ∈ U.map f ↔ f (a*x*a⁻¹) ∈ U.map f
    rw [ha]
  have hn : a ∈ normalizer (S : Set A) := by
    apply mem_normalizer_iff.mpr
    intro x
    rw [←hmem _ hkerS]
    constructor
    · intro hx
      exact hS ▸ mem_map_of_mem α.toMonoidHom hx
    · intro hx
      have hh : α x ∈ (S : Subgroup A).map α.toMonoidHom := hS.symm ▸ hx
      obtain ⟨y,hy,he⟩ := hh
      exact α.injective he ▸ hy
  have haS : a ∈ (S : Subgroup A) := self_normalizing_sylow S f hf hk e ▸ hn
  apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective α.injective])
  rintro _ ⟨x,hx,rfl⟩
  exact (hmem B hkerB x).mpr (B.mul_mem (B.mul_mem (hSB haS) hx) (B.inv_mem (hSB haS)))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction
open scoped IsMulCommutative
variable {X : Type*} [Group X] [IsElementaryAbelian 2 X]

theorem image_normalizer_inner (H : Subgroup (MulAut X))
    (hm : let θ := Representation.ofElementaryAbelianAction (A := H) (G := X) (p := 2)
      HasModelOn θ ⊤ (subspaceCommutator θ ⊤ ⊤) (binaryLinearAction 3))
    (β : MulAut X) (hβ : β ∈ normalizer (H : Set (MulAut X))) :
    ∃ a : H, ∀ x : H, β * (x : MulAut X) * β⁻¹ = (a : MulAut X) * x * (a : MulAut X)⁻¹ := by
  let α := H.normalizerMonoidHom ⟨β,hβ⟩
  let b : Additive X ≃ₗ[ZMod 2] Additive X :=
    β.toAdditive.toLinearEquiv (fun c x => ZMod.map_smul β.toAdditive.toAddMonoidHom c x)
  obtain ⟨a,ha⟩ := compatible_inner hm α b (by
    intro x v
    apply Additive.toMul.injective
    change β ((x : MulAut X) v.toMul) =
      (β * (x : MulAut X) * β⁻¹) (β v.toMul)
    simp)
  refine ⟨a,fun x => ?_⟩
  exact congrArg Subtype.val (congrArg (fun f : MulAut H => f x) ha)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction
open scoped IsMulCommutative
variable {G X : Type*} [Group G] [Finite G] [Group X] [IsElementaryAbelian 2 X]

theorem action_normalizes_overgroup (S : Sylow 2 G) (f : G →* MulAut X)
    (hk : IsPGroup 2 f.ker) (e : f.range ≃* BinaryLinear.OuterCyclic.LinearGroup 3)
    (hm : let θ := Representation.ofElementaryAbelianAction (A := f.range) (G := X) (p := 2)
      HasModelOn θ ⊤ (subspaceCommutator θ ⊤ ⊤) (binaryLinearAction 3))
    (α : MulAut G) (hS : (S : Subgroup G).map α.toMonoidHom = S)
    (β : MulAut X) (hβ : ∀ x, f (α x) = β * f x * β⁻¹)
    (B : Subgroup G) (hSB : (S : Subgroup G) ≤ B) : B.map α.toMonoidHom = B := by
  have hn : β ∈ normalizer (f.range : Set (MulAut X)) := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨α y,hβ y⟩
    · rintro ⟨y,hy⟩
      refine ⟨α.symm y,?_⟩
      have hh := hβ (α.symm y)
      rw [α.apply_symm_apply,hy] at hh
      exact mul_left_cancel (mul_right_cancel hh.symm)
  obtain ⟨a,ha⟩ := image_normalizer_inner f.range hm β hn
  obtain ⟨g,hg⟩ := f.rangeRestrict_surjective a
  have he (x : G) : f.rangeRestrict (α x) = f.rangeRestrict (g*x*g⁻¹) := by
    apply Subtype.ext
    change f (α x) = f (g*x*g⁻¹)
    rw [hβ]
    have hax : β * f x * β⁻¹ = (a : MulAut X) * f x * (a : MulAut X)⁻¹ := ha (f.rangeRestrict x)
    rw [hax,map_mul,map_mul,map_inv]
    exact congrArg (fun z : MulAut X => z * f x * z⁻¹) (congrArg Subtype.val hg).symm
  exact covariant_normalizes_overgroup S f.rangeRestrict f.rangeRestrict_surjective
    (by rw [MonoidHom.ker_rangeRestrict]; exact hk) e α hS g he B hSB

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction


namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

theorem quotient_action_normalizes_parabolic
    (T : Sylow 2 G) (K W Z B : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKW : K ≤ normalizer (W : Set G))
    [hZ : (Z.subgroupOf W).Normal]
    (f : K →* MulAut (W ⧸ Z.subgroupOf W))
    (hf : ∀ k : K, ∀ w : W,
      f k (QuotientGroup.mk' (Z.subgroupOf W) w) =
        QuotientGroup.mk' (Z.subgroupOf W)
          ⟨(k : G)*(w : G)*(k : G)⁻¹,(mem_normalizer_iff.mp (hKW k.property) w).mp w.property⟩)
    (hk : IsPGroup 2 f.ker)
    (e : f.range ≃* BinaryLinear.OuterCyclic.LinearGroup 3)
    (hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W))
    (hm : letI := hX
      let θ := Representation.ofElementaryAbelianAction
        (A := f.range) (G := W ⧸ Z.subgroupOf W) (p := 2)
      HasModelOn θ ⊤ (subspaceCommutator θ ⊤ ⊤) (binaryLinearAction 3))
    (hBK : B ≤ K) (hSB : (T : Subgroup G) ⊓ K ≤ B)
    {c : G} (hcK : c ∈ normalizer (K : Set G))
    (hcW : c ∈ normalizer (W : Set G)) (hcZ : c ∈ normalizer (Z : Set G))
    (hcS : c ∈ normalizer (((T : Subgroup G) ⊓ K : Subgroup G) : Set G)) :
    c ∈ normalizer (B : Set G) := by
  let := hX
  let J := normalizer (W : Set G) ⊓ normalizer (Z : Set G)
  obtain ⟨τ,hτ⟩ := exists_quotient_conjugation_action J W Z inf_le_left inf_le_right hZ
  let β := τ ⟨c,hcW,hcZ⟩
  let α := K.normalizerMonoidHom ⟨c,hcK⟩
  have hcov (k : K) : f (α k) * β = β * f k := by
    apply MulEquiv.ext
    intro x
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) x
    change f (α k) (β (QuotientGroup.mk' _ w)) = β (f k (QuotientGroup.mk' _ w))
    rw [show β (QuotientGroup.mk' _ w) = _ from hτ ⟨c,hcW,hcZ⟩ w,hf,hf,hτ]
    congr 1
    apply Subtype.ext
    change (c*(k:G)*c⁻¹)*(c*(w:G)*c⁻¹)*(c*(k:G)*c⁻¹)⁻¹ =
      c*((k:G)*(w:G)*(k:G)⁻¹)*c⁻¹
    group
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  have hmapS : (S : Subgroup K).map K.subtype = (T : Subgroup G) ⊓ K := by
    rw [hS,subgroupOf_map_subtype]
  have hαS : (S : Subgroup K).map α.toMonoidHom = S := by
    apply map_injective K.subtype_injective
    rw [map_map]
    have he : K.subtype.comp α.toMonoidHom = (MulAut.conj c).toMonoidHom.comp K.subtype := rfl
    rw [he,←map_map,hmapS]
    exact mem_normalizer_iff_map_conj_eq.mp hcS
  have he := action_normalizes_overgroup S f hk e hm α hαS β
    (fun k => (eq_mul_inv_iff_mul_eq).mpr (hcov k)) (B.subgroupOf K) (by
      rw [hS]
      exact fun k hk => hSB ⟨hk,k.property⟩)
  have hmapB := map_subgroupOf_eq_of_le hBK
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hh := congrArg (map K.subtype) he
  rw [map_map] at hh
  have he' : K.subtype.comp α.toMonoidHom = (MulAut.conj c).toMonoidHom.comp K.subtype := rfl
  rwa [he',←map_map,hmapB] at hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalThreeAction
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterG.Section06 CFSG.Quasithin.ChapterE
open scoped IsMulCommutative Classical
universe v
variable {G : Type v} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
namespace NaturalEscapeGraph.OddConfiguration
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d

/-- On the same original marked action, the full factor cover is invariant
under the entire central-line normalizer, including T. The symmetric-three
row gives the literal group generated by P and T with Sylow index three. -/
theorem exists_ambient_marked_cover
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let N := Escape.H (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N) (_hIN : I ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      let := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        let := hX
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Bijective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧ g.ker = pCore 2 P ∧
            (Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5))) ∧
            ((pResidual 2 P).map P.subtype = (primeToResidual 3 I).map I.subtype) ∧
            (N ≤ Subgroup.normalizer ((pResidual 2 P).map P.subtype : Set G)) ∧
            NaturalInvariantCoverData T P I N σ hPI ∧
            (Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) →
              let θ := Representation.ofElementaryAbelianAction
                (A := g.range) (G := W ⧸ Z.subgroupOf W) (p := 2)
              ChapterG.Section06.HasModelOn θ ⊤
                (Representation.BinaryOffender.subspaceCommutator θ ⊤ ⊤)
                (ChapterG.Section06.binaryLinearAction 3)) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,_hgen,product,hsingle,_hsmall,hmodels,
      hcanonical,hnormal,_horiginal,_hfactor,_hres,_hact,_hfull,_hrange,_hlift,_e,_he,_hcoords⟩ :=
    d.exists_ambient_canonical_residual h hnat hE hs hNS hab
  let := hZ
  let := hX
  let I := Escape.I (T : Subgroup G) L R
  let N := Escape.H (T : Subgroup G) L R
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let P := conjugateSpanBy E I
  let K := P ⊔ N.pCoreIn 2
  obtain ⟨hNK,hcore,⟨eK⟩⟩ := NaturalInvariantCover.invariant_cover_of_residual P I N hPI hPN
    (le_normalizer_conjugateSpanBy E I)
    (normal_subgroupOf_centralizer_normalizer (ZS (T : Subgroup G) L R : Set G))
    hnormal j hj hje hmodels
  have hKI : K ≤ I := sup_le hPI
    (natural_four_normalizer_core_centralizes (hn ▸ h) (hn ▸ hnat))
  have hTK : (T : Subgroup G) ≤ Subgroup.normalizer (K : Set G) :=
    h.sylow_normalizes_ZS.trans hNK
  let Z := ZS (T : Subgroup G) L R
  let W := Escape.U (T : Subgroup G) L R ⊓ conjugateSpanBy Z (centralizer ({z} : Set G))
  let g := σ.comp (inclusion hPI)
  let gK := σ.comp (inclusion hKI)
  have hQI : N.pCoreIn 2 ≤ I := natural_four_normalizer_core_centralizes (hn ▸ h) (hn ▸ hnat)
  have hQcore : N.pCoreIn 2 ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 N) hQI
    (hIN.trans (N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))))
  have hcI : (I.pCoreIn 2).subgroupOf I ≤ σ.ker :=
    quotient_conjugation_action_kills_commutator_layer I W Z (I.pCoreIn 2)
      hZ hIW ((commutator_mono inf_le_left le_rfl).trans (natural_escape_core h hnat).2) σ hσ
  have hQker : (N.pCoreIn 2).subgroupOf I ≤ σ.ker := (subgroupOf_mono I hQcore).trans hcI
  have hrangeK : gK.range = g.range := by
    change (σ.comp (inclusion hKI)).range = (σ.comp (inclusion hPI)).range
    rw [MonoidHom.range_comp,MonoidHom.range_comp,inclusion_range,inclusion_range]
    change ((P ⊔ N.pCoreIn 2).subgroupOf I).map σ = (P.subgroupOf I).map σ
    rw [subgroupOf_sup hPI hQI,Subgroup.map_sup,(Subgroup.map_eq_bot_iff _).mpr hQker,sup_bot_eq]
  have hkerK : gK.ker = pCore 2 K := by
    have hle : pCore 2 K ≤ gK.ker := by
      intro k hk
      apply hQker
      have hh : (k : G) ∈ K.pCoreIn 2 := mem_map_of_mem K.subtype hk
      exact hcore ▸ hh
    have hi : gK.ker.index = (pCore 2 K).index := by
      rw [index_ker,hrangeK,index_eq_card,Nat.card_congr eK.toEquiv]
      exact (Nat.card_congr (MulEquiv.ofBijective φ hφ).toEquiv).symm
    have hc := (pCore 2 K).card_mul_index
    have hd := gK.ker.card_mul_index
    rw [hi] at hd
    have hp : 0 < (pCore 2 K).index := Nat.pos_of_ne_zero (pCore 2 K).index_ne_zero_of_finite
    have he : Nat.card (pCore 2 K) = Nat.card gK.ker :=
      mul_right_cancel₀ (ne_of_gt hp) (hc.trans hd.symm)
    exact (eq_of_le_of_card_ge hle he.ge).symm
  have hS3 := NaturalInvariantCover.cubic_sylow_extension T P N
    h.sylow_normalizes_ZS hNK eK
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,
    hcanonical,hnormal,⟨hKI,hNK,hTK,hcore,⟨eK⟩,hrangeK,hkerK,hS3⟩,?_⟩
  rintro ⟨eP⟩
  apply NaturalThreeAction.canonical_model product hsingle
  let e := (MulEquiv.ofBijective φ hφ).symm.trans
    (eP.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm)
  exact (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_SL

end NaturalEscapeGraph.OddConfiguration
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

