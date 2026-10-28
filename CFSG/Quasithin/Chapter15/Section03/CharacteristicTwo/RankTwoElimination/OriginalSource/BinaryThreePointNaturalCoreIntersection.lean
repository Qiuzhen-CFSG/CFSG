module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointExteriorExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourCenterIntersection

/-!
# The natural point span meets the original core in exactly the natural eight

The actual span has order sixteen after exclusion of the exterior model.
Its intersection with Q centralizes Phi(Q) and has Frattini intersection V
of order eight. Its image in the marked doubled-dual middle section has
order at most two. Irreducibility of either three-dimensional projection
forces that image to vanish. Thus W intersects Q in exactly V; the extra
point-span involution is outside the original core.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open BinaryEndpointInduction
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem small_double_eq_bot
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : Representation (ZMod 2) A V) [IsIrreducible σ]
    (U : Subrepresentation (σ.prod σ)) (hc : Nat.card U.toSubmodule < Nat.card V) : U = ⊥ := by
  let F : Subrepresentation σ := {
    toSubmodule := U.toSubmodule.map (LinearMap.fst (ZMod 2) V V)
    apply_mem_toSubmodule g := by
      rintro _ ⟨x,hx,rfl⟩
      exact ⟨(σ.prod σ) g x,U.apply_mem_toSubmodule g hx,rfl⟩ }
  let E : Subrepresentation σ := {
    toSubmodule := U.toSubmodule.map (LinearMap.snd (ZMod 2) V V)
    apply_mem_toSubmodule g := by
      rintro _ ⟨x,hx,rfl⟩
      exact ⟨(σ.prod σ) g x,U.apply_mem_toSubmodule g hx,rfl⟩ }
  have hFcard : Nat.card F.toSubmodule ≤ Nat.card U.toSubmodule := by
    apply Nat.card_le_card_of_surjective (fun x : U.toSubmodule =>
      (⟨x.val.1,⟨x.val,x.property,rfl⟩⟩ : F.toSubmodule))
    rintro ⟨y,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  have hEcard : Nat.card E.toSubmodule ≤ Nat.card U.toSubmodule := by
    apply Nat.card_le_card_of_surjective (fun x : U.toSubmodule =>
      (⟨x.val.2,⟨x.val,x.property,rfl⟩⟩ : E.toSubmodule))
    rintro ⟨y,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  have hF : F = ⊥ := (eq_bot_or_eq_top F).resolve_right (by
    intro ht
    have hh : Nat.card F.toSubmodule = Nat.card V := by
      rw [ht]
      exact Nat.card_congr (Submodule.topEquiv).toEquiv
    omega)
  have hE : E = ⊥ := (eq_bot_or_eq_top E).resolve_right (by
    intro ht
    have hh : Nat.card E.toSubmodule = Nat.card V := by
      rw [ht]
      exact Nat.card_congr (Submodule.topEquiv).toEquiv
    omega)
  apply le_bot_iff.mp
  intro x hx
  have hx₁ : x.1 ∈ F := ⟨x,hx,rfl⟩
  have hx₂ : x.2 ∈ E := ⟨x,hx,rfl⟩
  rw [hF] at hx₁
  rw [hE] at hx₂
  exact Prod.ext hx₁ hx₂

private theorem small_double_section_le_kernel
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {L D E T : Subgroup G} {a : L →* A} {σ : Representation (ZMod 2) A V}
    [IsIrreducible σ]
    (ha : Function.Surjective a) (hs : HasSectionModel L D E a (σ.prod σ))
    (hTD : T ≤ D) (hLT : L ≤ normalizer T)
    (hc : Nat.card T < Nat.card V * Nat.card (T ⊓ E : Subgroup G)) : T ≤ E := by
  obtain ⟨hE,hLD,_,hn,e,he⟩ := hs
  let := hn
  let p := e.toMonoidHom.comp (QuotientGroup.mk' (E.subgroupOf D))
  have hk : p.ker = E.subgroupOf D := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let U : Subrepresentation (σ.prod σ) := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 ((T.subgroupOf D).map p).toAddSubgroup'
    apply_mem_toSubmodule g := by
      intro v hv
      obtain ⟨l,rfl⟩ := ha g
      change Multiplicative.ofAdd v ∈ (T.subgroupOf D).map p at hv
      obtain ⟨x,hx,hv⟩ := hv
      let y := D.normalizerMonoidHom (inclusion hLD l) x
      have hyT : (y : G) ∈ T := (mem_normalizer_iff.mp (hLT l.property) x).mp hx
      change Multiplicative.ofAdd ((σ.prod σ) (a l) v) ∈ (T.subgroupOf D).map p
      refine ⟨y,hyT,?_⟩
      apply Multiplicative.toAdd.injective
      have hh := he l x y rfl
      change (p y).toAdd = (σ.prod σ) (a l) (p x).toAdd at hh
      rw [hh,hv]
      rfl }
  let f := p.comp (inclusion hTD)
  have hfr : f.range = (T.subgroupOf D).map p := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨inclusion hTD t,t.property,rfl⟩
    · rintro ⟨d,hd,rfl⟩
      exact ⟨⟨d,hd⟩,rfl⟩
  have hfk : f.ker = (T ⊓ E).subgroupOf T := by
    ext x
    change p (inclusion hTD x) = 1 ↔ (x : G) ∈ T ⊓ E
    have hh : p (inclusion hTD x)=1 ↔ (x : G)∈E := by
      change inclusion hTD x ∈ p.ker ↔ _
      rw [hk]
      rfl
    exact hh.trans (and_iff_right x.property).symm
  have hcard : Nat.card T = Nat.card U.toSubmodule * Nat.card (T ⊓ E : Subgroup G) := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hfr,hfk,
      Nat.card_congr (subgroupOfEquivOfLe (show T ⊓ E ≤ T from inf_le_left)).toEquiv]
    rfl
  have hsmall : Nat.card U.toSubmodule < Nat.card V := by
    rw [hcard] at hc
    exact (Nat.mul_lt_mul_right (Nat.card_pos (α := (T ⊓ E : Subgroup G)))).mp hc
  have hbot := small_double_eq_bot σ U hsmall
  intro t ht
  have hm : (p ⟨t,hTD ht⟩).toAdd ∈ U := mem_map_of_mem p ht
  rw [hbot] at hm
  have htker : (⟨t,hTD ht⟩ : D) ∈ p.ker := hm
  rw [hk] at htker
  exact htker

/-- The original natural four-span has precisely its natural eight inside Q. -/
theorem binary_three_source_natural_core_intersection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2)
    (hz : z ∈ intrinsicFour c.L) (hz1 : z ≠ 1) :
    let Q := LinearThree.commutatorCore c.L
    let V := ⁅coreCenter c.L,c.L⁆
    let W := conjugateSpanBy V (centralizer ({z} : Set G))
    Nat.card W = 16 ∧ W ⊓ Q = V ∧ ¬ W ≤ Q := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let Q := LinearThree.commutatorCore c.L
  let Phi := frattiniIn Q
  let D := Q ⊓ centralizer (Phi : Set G)
  let V := ⁅coreCenter c.L,c.L⁆
  let W := conjugateSpanBy V C
  let T := W ⊓ Q
  obtain ⟨hW,σ,_,_,_,_,_,E,_⟩ := binary_three_source_four_natural_model
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hz hz1
  let := hW
  have hWcard : Nat.card W = 16 := by
    change Nat.card (Additive W) = 16
    rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      Module.finrank_fin_fun,Nat.card_zmod]
    norm_num
  obtain ⟨_,hVcard,hVW,hWcenter,hCW,_⟩ := binary_three_source_binary_central_eight_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm
  have hWc : W ≤ centralizer (N : Set G) := by
    intro w hw
    obtain ⟨x,hx,rfl⟩ := hWcenter hw
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
  have hPhiN : Phi ≤ N := binary_three_source_binary_phi_kernel
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm
  have hTD : T ≤ D := le_inf inf_le_right
    (inf_le_left.trans (hWc.trans (centralizer_le hPhiN)))
  have hLT : c.L ≤ normalizer T :=
    (le_inf ((le_sup_left.trans hLS).trans hCW)
      (c.L.le_normalizer.trans (normalizer_le_normalizer_commutatorCore c.L))).trans
        inf_normalizer_le_normalizer_inf
  have hPhiQ : Phi ≤ Q := map_subtype_le _
  have hWPhi : W ⊓ Phi = V := (binary_three_source_four_center_intersection
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm).2
  have hTPhi : T ⊓ Phi = V := by
    change (W ⊓ Q) ⊓ Phi = V
    rw [inf_assoc,inf_eq_right.mpr hPhiQ,hWPhi]
  have hTcard : Nat.card T ≤ 16 := (card_le_of_le (show T ≤ W from inf_le_left)).trans_eq hWcard
  obtain ⟨a,_,hs,_⟩ := binary_three_large_distance_original_core_sections
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb
  let : IsIrreducible BinaryLinearThree.W.dual := BinaryLinearThree.IrreducibleCatalogue.dual_irreducible
  let : Finite (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) := Module.finite_of_finite (ZMod 2)
  have h8 : Nat.card (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)) = 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,Subspace.dual_finrank_eq,
      Module.finrank_fin_fun]
    norm_num
  have hTP : T ≤ Phi := small_double_section_le_kernel
    (a.surjective.comp (QuotientGroup.mk'_surjective _)) hs hTD hLT (by
      rw [h8,hTPhi,hVcard]
      omega)
  have hTV : T = V := le_antisymm ((le_inf inf_le_left hTP).trans hWPhi.le)
    (hTPhi.symm.le.trans inf_le_left)
  refine ⟨hWcard,hTV,?_⟩
  intro hWQ
  have hh : W = V := (inf_eq_left.mpr hWQ).symm.trans hTV
  rw [hh,hVcard] at hWcard
  omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
