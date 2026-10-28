module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryMarkedParabolic
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryModuleRecognition

/-!
# Eliminating the marked middle-node binary-four escape

The middle-node parabolic in GL₄(2) preserves the first line and last
hyperplane of the original full flag. Over the binary field it therefore
fixes every flag-fixed vector and covector, also in repeated natural modules.
This gives a direct substitute for the outer-actor fixed-line calculation.

The residual embeds into the full moved module with individual centralization
detected in both directions. Transport of the exact two-core quotient and
both marked flags then makes its nontrivial Sylow-fixed subgroup centralize
the original cubic residual, contrary to their disjointness. The Chapter12
companion supplies all premises on the original chosen orbit.

Source: Aschbacher--Smith, proof after 7.7.10, printed p.709,
refs/quasithin.pdf, and B.5.1(1)(iii--iv), printed p.99.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFourAction
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
open ChapterB.QuasisimpleSource

private theorem binary_span_fixed (g : LinearGroup 4) {x : Space 4} (hx : x ≠ 0)
    (hg : g x ∈ Submodule.span (ZMod 2) {x}) : g x = x := by
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hg
  have hcx : c ≠ 0 := by
    intro hz
    rw [hz,zero_smul] at hc
    exact hx (g.injective (hc.symm.trans (map_zero g).symm))
  have hc1 : c = 1 := by revert hcx; fin_cases c <;> simp
  simpa only [hc1,one_smul] using hc.symm

/-- The middle-node parabolic fixes the full-flag fixed vectors of the natural module. -/
theorem middle_fixes_natural (b : Basis 3) (g : LinearGroup 4)
    (hg : g ∈ minimalParabolic b (1 : Fin 3)) (x : Space 4)
    (hx : ∀ s ∈ cutStabilizer b Set.univ, s x = x) : g x = x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  let W := Submodule.span (ZMod 2) {x}
  have hd : Module.finrank (ZMod 2) W = 1 := finrank_span_singleton hx0
  have hW0 : W ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hx0
  have hW1 : W ≠ ⊤ := by
    intro he
    rw [he,finrank_top,Module.finrank_fin_fun] at hd
    norm_num at hd
  have hn : cutStabilizer b Set.univ ≤ parabolic W := by
    intro s hs v
    constructor
    · intro hv
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hv
      apply Submodule.mem_span_singleton.mpr
      refine ⟨c,s.injective ?_⟩
      rw [map_smul,hx s hs,hc]
    · intro hv
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul,hx s hs]
      exact W.smul_mem c (Submodule.subset_span (Set.mem_singleton x))
  obtain ⟨i,hi⟩ := fullFlag_invariant_subspace b W hW0 hW1 hn
  have hid := congrArg (fun W : Submodule (ZMod 2) (Space 4) => Module.finrank (ZMod 2) W) hi
  rw [hd,cutSpace_finrank] at hid
  have hi0 : i = 0 := Fin.ext (by omega)
  have hgw : g x ∈ W := by
    rw [hi,hi0]
    apply ((mem_cutStabilizer b {(1 : Fin 3)}ᶜ g).mp hg 0 (by decide) x).mpr
    rw [←hi0,←hi]
    exact Submodule.subset_span (Set.mem_singleton x)
  exact binary_span_fixed g hx0 hgw

/-- The same marked parabolic fixes the full-flag fixed covectors. -/
theorem middle_fixes_dual (b : Basis 3) (g : LinearGroup 4)
    (hg : g ∈ minimalParabolic b (1 : Fin 3)) (f : Module.Dual (ZMod 2) (Space 4))
    (hf : ∀ s ∈ cutStabilizer b Set.univ, s.symm.dualMap f = f) :
    g.symm.dualMap f = f := by
  by_cases hf0 : f = 0
  · simp [hf0]
  have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hf0
  rw [Module.finrank_fin_fun] at hd
  have hW0 : f.ker ≠ ⊥ := by intro he; rw [he,finrank_bot] at hd; omega
  have hW1 : f.ker ≠ ⊤ := by intro he; rw [he,finrank_top,Module.finrank_fin_fun] at hd; omega
  have hn : cutStabilizer b Set.univ ≤ parabolic f.ker := by
    intro s hs v
    have hh := LinearMap.congr_fun (hf s⁻¹ ((cutStabilizer b Set.univ).inv_mem hs)) v
    change f (s v) = f v at hh
    change f (s v) = 0 ↔ f v = 0
    rw [hh]
  obtain ⟨i,hi⟩ := fullFlag_invariant_subspace b f.ker hW0 hW1 hn
  have hid := congrArg (fun W : Submodule (ZMod 2) (Space 4) => Module.finrank (ZMod 2) W) hi
  rw [cutSpace_finrank] at hid
  have hi2 : i = 2 := Fin.ext (by omega)
  apply LinearMap.ext
  intro x
  have hh := (mem_cutStabilizer b {(1 : Fin 3)}ᶜ g⁻¹).mp
    ((minimalParabolic b 1).inv_mem hg) 2 (by decide) x
  rw [←hi2,←hi] at hh
  change f (g.symm x) = 0 ↔ f x = 0 at hh
  change f (g.symm x) = f x
  revert hh
  generalize f (g.symm x) = a
  generalize f x = c
  fin_cases a <;> fin_cases c <;> simp

/-- The middle node fixes all flag-fixed elements in the natural--dual model. -/
theorem middle_fixes_naturalDual (b : Basis 3) (g : SL(4,ZMod 2))
    (hg : slEquivLinear 4 g ∈ minimalParabolic b (1 : Fin 3))
    (v : (Space 4) × Module.Dual (ZMod 2) (Space 4))
    (hv : ∀ s : SL(4,ZMod 2), slEquivLinear 4 s ∈ cutStabilizer b Set.univ →
      naturalPlusDual 4 s v = v) : naturalPlusDual 4 g v = v := by
  change NaturalDualCentralizer.slAction 4 g v = v
  rw [NaturalDualCentralizer.action_apply,BinaryNaturalDual.naturalDualRepresentation_apply]
  apply Prod.ext
  · apply middle_fixes_natural b _ hg
    intro s hs
    obtain ⟨s,rfl⟩ := (slEquivLinear 4).surjective s
    have hh0 := hv s hs
    change NaturalDualCentralizer.slAction 4 s v = v at hh0
    have hh := congrArg Prod.fst hh0
    simpa only [NaturalDualCentralizer.action_apply,BinaryNaturalDual.naturalDualRepresentation_apply]
      using hh
  · apply middle_fixes_dual b _ hg
    intro s hs
    obtain ⟨s,rfl⟩ := (slEquivLinear 4).surjective s
    have hh0 := hv s hs
    change NaturalDualCentralizer.slAction 4 s v = v at hh0
    have hh := congrArg Prod.snd hh0
    simpa only [NaturalDualCentralizer.action_apply,BinaryNaturalDual.naturalDualRepresentation_apply]
      using hh

/-- The same assertion holds for any number of equal natural copies. -/
theorem middle_fixes_repeated (b : Basis 3) (g : SL(4,ZMod 2))
    (hg : slEquivLinear 4 g ∈ minimalParabolic b (1 : Fin 3)) (r : ℕ)
    (v : Fin r → Space 4)
    (hv : ∀ s : SL(4,ZMod 2), slEquivLinear 4 s ∈ cutStabilizer b Set.univ →
      repeated (linearNatural BinaryField.two 4) r s v = v) :
    repeated (linearNatural BinaryField.two 4) r g v = v := by
  funext i
  change linearNatural BinaryField.two 4 g (v i) = v i
  change specialLinearNatural 4 g (v i) = v i
  rw [specialLinearNatural_apply,←slEquivLinear_apply]
  apply middle_fixes_natural b _ hg
  intro s hs
  obtain ⟨s,rfl⟩ := (slEquivLinear 4).surjective s
  have hh := congrFun (hv s hs) i
  change specialLinearNatural 4 s (v i) = v i at hh
  rwa [specialLinearNatural_apply,←slEquivLinear_apply] at hh

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] {K Q : Subgroup G}

/-- The full moved embedding detects individual centralization in both directions. -/
theorem star_moved_embedding_fixed_iff
    (W A X : Subgroup G) (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hX : X = ⁅W,A⁆) [IsElementaryAbelian 2 X]
    {J : Subgroup (StarQuotient K Q)} (hCJ : starImage K Q K ≤ J)
    (s : MovedSection ((starRepresentation K Q).comp J.subtype)
      ((starImage K Q K).subgroupOf J)) :
    ∃ f : Additive X →ₗ[ZMod 2] s.space.toSubmodule,
      Function.Injective f ∧ ∀ (k : K) (x : Additive X),
        (s.space.toRepresentation.comp ((starImage K Q K).subgroupOf J).subtype)
          ((subgroupOfEquivOfLe hCJ).symm (toStarImage K Q k)) (f x) = f x ↔
          (k : G) * (x.toMul : G) = (x.toMul : G) * k := by
  let U := starV K Q
  let KJ := K.subgroupOf (K ⊔ Q)
  let XJ := ⁅U,KJ⁆
  have hXJ : X ≤ XJ.map (K ⊔ Q : Subgroup G).subtype := by
    rw [hX,map_commutator,map_subgroupOf_eq_of_le (show K ≤ K ⊔ Q from le_sup_left)]
    exact commutator_mono hWX hAK
  let j : X →* XJ := {
    toFun x := ⟨⟨x,(map_subtype_le XJ) (hXJ x.property)⟩,by
      obtain ⟨y,hy,he⟩ := hXJ x.property
      exact (Subtype.ext he : y = ⟨x,_⟩) ▸ hy⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let : IsElementaryAbelian 2 XJ := IsElementaryAbelian.of_injective
    (inclusion (commutator_le_left U KJ)) (inclusion_injective _)
  let q := QuotientGroup.mk' (starKernel K Q)
  have hs : s.space.toSubmodule = subspaceCommutator (starRepresentation K Q) ⊤ (KJ.map q) := by
    rw [s.space_eq]
    change subspaceCommutator ((starRepresentation K Q).comp J.subtype) ⊤
      ((starImage K Q K).subgroupOf J) = _
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hCJ]
    rfl
  let a := (NormalElementaryQuotient.movedEquiv U q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) KJ).trans (LinearEquiv.ofEq _ _ hs.symm)
  let f : Additive X →ₗ[ZMod 2] s.space.toSubmodule :=
    a.toLinearMap.comp (j.toAdditive.toZModLinearMap 2)
  have hf (x : Additive X) : ((f x).val.toMul.val.val : G) = x.toMul.val := rfl
  refine ⟨f,?_,?_⟩
  · intro x y he
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun z : s.space.toSubmodule => (z.val.toMul.val.val : G)) he
  · intro k x
    have hh := NormalElementaryQuotient.representation_apply U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      (inclusion (show K ≤ K ⊔ Q from le_sup_left) k) (f x).val
    have he : (((s.space.toRepresentation.comp ((starImage K Q K).subgroupOf J).subtype)
        ((subgroupOfEquivOfLe hCJ).symm (toStarImage K Q k)) (f x)).val.toMul.val.val : G) =
        (k : G) * (x.toMul : G) * (k : G)⁻¹ := congrArg Subtype.val hh
    constructor
    · intro hfix
      have hc := congrArg (fun z : s.space.toSubmodule => (z.val.toMul.val.val : G)) hfix
      rw [he,hf] at hc
      exact (mul_inv_eq_iff_eq_mul).mp hc
    · intro hc
      apply Subtype.ext
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      rw [he,hf,hc,mul_inv_cancel_right]

/-- Retain the marked middle node for an arbitrary surjection with the same full kernel. -/
theorem middle_of_projection (K A R : Subgroup G)
    (hc : DoubledBinaryMarkedParabolic.Conclusion K A R)
    (q : K →* SL(4,ZMod 2)) (hq : Function.Surjective q) (hk : q.ker = pCore 2 K) :
    ∃ b : Basis 3,
      (R.subgroupOf K).map ((slEquivLinear 4).toMonoidHom.comp q) = cutStabilizer b Set.univ ∧
      ((A ⊔ R).subgroupOf K).map ((slEquivLinear 4).toMonoidHom.comp q) =
        minimalParabolic b (1 : Fin 3) := by
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have he : coreFlagMap K e = (slEquivLinear 4).toMonoidHom.comp q := by
    ext k
    rfl
  obtain ⟨_,b,i,hR,hA,_,_,hi⟩ := hc.2 e
  have hi1 : i = 1 := Fin.ext (by omega)
  exact ⟨b,he ▸ hR,by simpa only [hi1,he] using hA⟩

/-- Passage from an internal component to its ambient image keeps the same two marked flags. -/
theorem middle_in_ambient (H : Subgroup G) (C : Subgroup H) (A R : Subgroup G)
    (hc : DoubledBinaryMarkedParabolic.Conclusion C (A.subgroupOf H) (R.subgroupOf H))
    (q : C.map H.subtype →* SL(4,ZMod 2)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (C.map H.subtype)) :
    ∃ b : Basis 3,
      (R.subgroupOf (C.map H.subtype)).map ((slEquivLinear 4).toMonoidHom.comp q) =
        cutStabilizer b Set.univ ∧
      (A.subgroupOf (C.map H.subtype)).map ((slEquivLinear 4).toMonoidHom.comp q) ≤
        minimalParabolic b (1 : Fin 3) := by
  let e := C.equivMapOfInjective H.subtype H.subtype_injective
  let p := q.comp e.toMonoidHom
  have hp : p.ker = pCore 2 C := by
    change q.ker.comap e.toMonoidHom = pCore 2 C
    rw [hk,←pCore_map_iso 2 e]
    exact comap_map_eq_self_of_injective e.injective _
  obtain ⟨b,hR,hB⟩ := middle_of_projection C (A.subgroupOf H) (R.subgroupOf H)
    hc p (hq.comp e.surjective) hp
  have hs (X : Subgroup G) :
      ((X.subgroupOf H).subgroupOf C).map e.toMonoidHom = X.subgroupOf (C.map H.subtype) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      obtain ⟨y,rfl⟩ := e.surjective x
      exact ⟨y,hx,rfl⟩
  refine ⟨b,?_,?_⟩
  · rw [←hs R,map_map]
    exact hR
  · rw [←hs A,map_map]
    exact (map_mono (subgroupOf_mono C (show A.subgroupOf H ≤
      A.subgroupOf H ⊔ R.subgroupOf H from le_sup_left))).trans hB.le

private theorem no_middle_model
    (W A X R Z : Subgroup G)
    (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hX : X = ⁅W,A⁆)
    (hdis : Disjoint X (centralizer (A : Set G))) [IsElementaryAbelian 2 X]
    (hZX : Z ≤ X) (hZR : Z ≤ centralizer (R : Set G)) (hZ : Z ≠ ⊥)
    {J : Subgroup (StarQuotient K Q)} (hCJ : starImage K Q K ≤ J)
    (s : MovedSection ((starRepresentation K Q).comp J.subtype)
      ((starImage K Q K).subgroupOf J))
    (hk : (toStarImage K Q).ker = pCore 2 K)
    (hm : ∀ (q : K →* SL(4,ZMod 2)), Function.Surjective q → q.ker = pCore 2 K →
      ∃ b : Basis 3,
        (R.subgroupOf K).map ((slEquivLinear 4).toMonoidHom.comp q) = cutStabilizer b Set.univ ∧
        (A.subgroupOf K).map ((slEquivLinear 4).toMonoidHom.comp q) ≤ minimalParabolic b 1)
    {V₁ : Type*} [AddCommGroup V₁] [Module (ZMod 2) V₁]
    (σ : Representation (ZMod 2) SL(4,ZMod 2) V₁)
    (a : ActionEquiv (s.space.toRepresentation.comp ((starImage K Q K).subgroupOf J).subtype) σ)
    (hmodel : ∀ (b : Basis 3) (g : SL(4,ZMod 2)),
      slEquivLinear 4 g ∈ minimalParabolic b 1 → ∀ v : V₁,
      (∀ t : SL(4,ZMod 2), slEquivLinear 4 t ∈ cutStabilizer b Set.univ → σ t v = v) →
      σ g v = v) : False := by
  obtain ⟨j,_,hfix⟩ := star_moved_embedding_fixed_iff W A X hWX hAK hX hCJ s
  let q := starMovedProjection hCJ a.groupEquiv
  have hq : Function.Surjective q := starMovedProjection_surjective hCJ a.groupEquiv
  have hkq : q.ker = pCore 2 K := by
    ext k
    change q k = 1 ↔ k ∈ pCore 2 K
    rw [starMovedProjection_apply, a.groupEquiv.map_eq_one_iff,
      (subgroupOfEquivOfLe hCJ).symm.map_eq_one_iff]
    exact Iff.of_eq (congrArg (fun P : Subgroup K => k ∈ P) hk)
  obtain ⟨b,hR,hA⟩ := hm q hq hkq
  have hZA : Z ≤ centralizer (A : Set G) := by
    intro z hz k hkA
    let x : Additive X := Additive.ofMul ⟨z,hZX hz⟩
    let k₀ : K := ⟨k,hAK hkA⟩
    have hkmodel : slEquivLinear 4 (q k₀) ∈ minimalParabolic b 1 :=
      hA (mem_map_of_mem _ hkA)
    have hh := hmodel b (q k₀) hkmodel (a.linearEquiv (j x)) (by
      intro t ht
      obtain ⟨r,hr,he⟩ := (hR.symm ▸ ht)
      have he' : q r = t := (slEquivLinear 4).injective he
      rw [←he',starMovedProjection_apply,←a.intertwines]
      apply congrArg a.linearEquiv
      exact (hfix r x).mpr (hZR hz r hr))
    rw [starMovedProjection_apply,←a.intertwines] at hh
    exact (hfix k₀ x).mp (a.linearEquiv.injective hh)
  exact hZ (le_bot_iff.mp (le_inf hZX hZA |>.trans (disjoint_iff.mp hdis).le))

/-- The marked middle parabolic excludes every surviving degree-four moved module. -/
theorem no_four_moved
    (W A X R Z : Subgroup G)
    (hWX : W ≤ (starV K Q).map (K ⊔ Q : Subgroup G).subtype)
    (hAK : A ≤ K) (hX : X = ⁅W,A⁆)
    (hdis : Disjoint X (centralizer (A : Set G))) [IsElementaryAbelian 2 X]
    (hZX : Z ≤ X) (hZR : Z ≤ centralizer (R : Set G)) (hZ : Z ≠ ⊥)
    {J : Subgroup (StarQuotient K Q)} (hCJ : starImage K Q K ≤ J)
    (s : MovedSection ((starRepresentation K Q).comp J.subtype)
      ((starImage K Q K).subgroupOf J))
    (hk : (toStarImage K Q).ker = pCore 2 K)
    (hm : ∀ (q : K →* SL(4,ZMod 2)), Function.Surjective q → q.ker = pCore 2 K →
      ∃ b : Basis 3,
        (R.subgroupOf K).map ((slEquivLinear 4).toMonoidHom.comp q) = cutStabilizer b Set.univ ∧
        (A.subgroupOf K).map ((slEquivLinear 4).toMonoidHom.comp q) ≤ minimalParabolic b 1)
    (hn : IsNaturalPlusDual (s.space.toRepresentation.comp
        ((starImage K Q K).subgroupOf J).subtype) 4 ∨
      ∃ r : ℕ, 2 ≤ r ∧ r ≤ 3 ∧ IsRepeatedLinearNatural
        (s.space.toRepresentation.comp ((starImage K Q K).subgroupOf J).subtype)
        BinaryField.two 4 r) : False := by
  rcases hn with hn | ⟨r,_,_,a⟩
  · obtain ⟨a⟩ := hn
    exact no_middle_model W A X R Z hWX hAK hX hdis hZX hZR hZ hCJ s hk hm
      (naturalPlusDual 4) a middle_fixes_naturalDual
  · obtain ⟨a⟩ := a
    exact no_middle_model W A X R Z hWX hAK hX hdis hZX hZR hZ hCJ s hk hm
      (repeated (linearNatural BinaryField.two 4) r) a
      (fun b g hg v hv => middle_fixes_repeated b g hg r v hv)

/-- After the marked degree-four exclusion only the binary three and the
full cubic cover of A₆ remain in the original star catalogue. -/
theorem remaining_three_or_tripleSix {D : Type*} [Group D]
    (h : DoubledBinaryStarRadicals.RemainingStarModel D)
    (h6 : ¬ Nonempty (D ≃* alternatingGroup (Fin 6)))
    (h7 : ¬ Nonempty (D ≃* alternatingGroup (Fin 7)))
    (hg : ¬ Nonempty (D ≃* commutator (Atlas.G2.Model (ZMod 2))))
    (h4 : ¬ Nonempty (D ≃* SL(4,ZMod 2)))
    (h5 : ¬ Nonempty (D ≃* SL(5,ZMod 2))) :
    Nonempty (D ≃* SL(3,ZMod 2)) ∨
      Nonempty (center D ≃* Multiplicative (ZMod 3)) ∧
      Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin 6)) := by
  rcases h with ⟨F,hF,⟨e⟩⟩ | ⟨n,hn,⟨e⟩⟩ | hg' | h5' | hc
  · exact Or.inl ⟨e.trans (ExtensionConsequences.degreeOneNaturalEquiv F hF 3).groupEquiv⟩
  · rcases hn with rfl | rfl | rfl
    · exact (h6 ⟨e⟩).elim
    · exact (h7 ⟨e⟩).elim
    · exact (h4 ⟨e.trans (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm.trans
        Atlas.Order20160A8.sl4TwoEquivPSL.symm)⟩).elim
  · exact (hg hg').elim
  · exact (h5 h5').elim
  · exact Or.inr hc

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryFourAction
