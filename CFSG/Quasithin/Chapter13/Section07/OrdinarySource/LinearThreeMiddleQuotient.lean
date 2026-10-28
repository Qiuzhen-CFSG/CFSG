module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeC3Local
public import Theory.GroupTheory.SymmetricThreeProductLocalMaps
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeCoreImage

/-!
# The product quotient of the actual middle C₃ vertex

The quotient of K₀T by its two-core extends across the normalized plane actor
L₂: their intersection is a normal two-group. Pair this extension with the
literal action on V₂. The action kernel inside L₂ is a two-group and its image
has order three, so the joint kernel is a two-group. The original O₂(LT) fixes
V₂ but escapes O₂(K₀T), forcing the image to be the whole S₃ × S₃.

This constructs the quotient of the source subgroup K₀L₂T itself. The source
noncentrality, ordinary alternating-six quotient, and independent core image
are discharged from the original binary-three branch, with no independent
factor hypothesis.

Source: Aschbacher–Smith, proof of 13.7.6(1), printed p.940, using 13.5.4(1).
-/

@[expose] public section
open Subgroup Representation Module
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeC3Local
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component.RecognitionStep
open Section08.TransvectionParabolic.Marking
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Section05.PlaneGeometry.TwoBlocks Section05.AmbientSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- A point-centralizing element in L₂ acts trivially on the original plane. -/
theorem planeActor_inf_point_centralizer_le_core
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    planeActor (L := L) (V₂ := V₂) ⊓ centralizer (V₁ : Set G) ≤
      (planeActor (L := L) (V₂ := V₂)).pCoreIn 2 := by
  let := source_plane_isKleinFour d
  let X := planeActor (L := L) (V₂ := V₂)
  let N := normalizer (V₂ : Set G)
  let B := X ⊓ centralizer (V₁ : Set G)
  let A := (B.subgroupOf N).map V₂.normalizerMonoidHom
  have hX : X ≤ N := planeActor_le.trans inf_le_right
  have hcardX : Nat.card ((X.subgroupOf N).map V₂.normalizerMonoidHom) = 3 := by
    have hh := (Ordinary.planeActor_action_source d e).1
    rw [planeAction,←map_map] at hh
    rwa [card_map_of_injective (IsKleinFour.autEquivPermThree V₂).injective] at hh
  have hAdiv : Nat.card A ∣ 3 := hcardX ▸ card_dvd_of_le
    (map_mono (f := V₂.normalizerMonoidHom) (comap_mono (show B ≤ X from inf_le_left)))
  have hAle : Nat.card A ≤ 2 := by
    have hpoint : V₁ ≠ ⊥ := by
      intro hz
      have hh := d.line_card
      rw [hz,card_bot] at hh
      contradiction
    obtain ⟨z,hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hpoint
    let z₂ : V₂ := ⟨z,d.line_le_plane z.property⟩
    apply card_mulAut_subgroup_le_two_of_fixed_point d.plane_card z₂
      (fun he => hz (Subtype.ext (congrArg (fun w : V₂ => w.val) he))) A
    rintro a ⟨g,hg,rfl⟩
    apply Subtype.ext
    change g.val * z.val * g.val⁻¹ = z.val
    have hc := mem_centralizer_iff.mp hg.2 z.val z.property
    change z.val * g.val = g.val * z.val at hc
    rw [←hc,mul_inv_cancel_right]
  have hA : A = ⊥ := by
    apply card_eq_one.mp
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hAdiv with hh | hh
    · exact hh
    · omega
  rw [(Ordinary.planeActor_core_source d e).1]
  intro x hx
  refine ⟨hx.1,?_⟩
  have hax : V₂.normalizerMonoidHom ⟨x,hX hx.1⟩ = 1 := by
    have hh : V₂.normalizerMonoidHom ⟨x,hX hx.1⟩ ∈ A := ⟨⟨x,hX hx.1⟩,hx,rfl⟩
    rw [hA] at hh
    exact hh
  apply (planeAction_eq_one V₂ ⟨x,hX hx.1⟩).mp
  change IsKleinFour.autEquivPermThree V₂ (V₂.normalizerMonoidHom _) = 1
  rw [hax,map_one]

/-- The common part of L₂ and the H-plane parabolic is a two-group. -/
theorem planeActor_inf_H_isTwoGroup
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hH : H ≤ centralizer (V₁ : Set G)) :
    IsPGroup 2 (planeActor (L := L) (V₂ := V₂) ⊓ H : Subgroup G) :=
  (isPGroup_pCoreIn 2 _).to_le ((inf_le_inf_left _ hH).trans
    (planeActor_inf_point_centralizer_le_core d e))


/-- The literal source middle vertex has the required product quotient. -/
theorem middle_quotient
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 3) eK) :
    Nonempty ((middle T L K V₂ ⧸ pCore 2 (middle T L K V₂)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let := source_plane_isKleinFour d
  obtain ⟨_,⟨eL⟩,_⟩ := ModelExclusions.linear_three_source_setup_of_one_le
    d hH hF9 hKH hK hL₁K ρ hρ eK hs
  obtain ⟨hA,⟨eA⟩⟩ := point_parabolic d hH hF9 hKH hK hL₁K ρ hρ eK hs
  let A := pointResidual K V₂ ⊔ (T : Subgroup G)
  let X := planeActor (L := L) (V₂ := V₂)
  let J := A ⊔ X
  let N := normalizer (V₂ : Set G)
  have hJM : J = middle T L K V₂ := by dsimp [J,A,X,middle]; ac_rfl
  have hJN : J ≤ N := hJM ▸ middle_le_plane_normalizer d
  have hAX : A ≤ normalizer (X : Set G) :=
    (show A ≤ J from le_sup_left).trans (hJM ▸ middle_normalizes_planeActor d eL hm)
  have hAH : A ≤ H := hA.le.trans inf_le_left
  let f : A →* Equiv.Perm (Fin 3) := eA.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfk : f.ker = pCore 2 A := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ eA.injective,QuotientGroup.ker_mk']
  have hf2 : IsPGroup 2 f.ker := hfk ▸ pCore_isPGroup
  have hHC : H ≤ centralizer (V₁ : Set G) :=
    (hH.2.1.trans d.first_normalizer.le).trans (normalizer_le_centralizer_of_card_two V₁ d.line_card)
  have hXA2 : IsPGroup 2 (X.subgroupOf A) := by
    apply (planeActor_inf_H_isTwoGroup d eL hHC).comap_subtype.to_le
    intro a ha
    exact ⟨ha,hAH a.property⟩
  have hXA : X.subgroupOf A ≤ f.ker := by
    rw [hfk]
    let : (X.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hAX
    exact le_sSup ⟨inferInstance,hXA2⟩
  let g : J →* Equiv.Perm (Fin 3) := (planeAction V₂).comp (inclusion hJN)
  have hg : Function.Surjective g := by
    let P := planeLocal (L := L) (V₂ := V₂)
    let r : P →* Equiv.Perm (Fin 3) := (planeAction V₂).comp (inclusion (show P ≤ N from inf_le_right))
    obtain ⟨q,hq,_,hfix⟩ := Ordinary.exists_planeLocal_quotient d eL
    have hrk : r.ker = q.ker := by
      ext a
      exact (planeAction_eq_one V₂ (inclusion (show P ≤ N from inf_le_right) a)).trans (hfix a).symm
    have hr : Function.Surjective r := by
      apply MonoidHom.range_eq_top.mp
      apply r.range.eq_top_of_card_eq
      rw [←index_ker,hrk,index_ker,MonoidHom.range_eq_top.mpr hq,card_top]
    have hPJ : P ≤ J := by
      have hPB : P ≤ X ⊔ (T : Subgroup G) := by
        rw [planeActor_sup_sylow d]
        exact inf_le_inf_right N le_sup_left
      exact hPB.trans (sup_le le_sup_right (le_sup_right.trans le_sup_left))
    intro b
    obtain ⟨a,ha⟩ := hr b
    exact ⟨inclusion hPJ a,ha⟩
  have hXg : IsPGroup 2 (X.subgroupOf J ⊓ g.ker : Subgroup J) := by
    have he : X.subgroupOf J ⊓ g.ker = (X ⊓ centralizer (V₂ : Set G)).subgroupOf J := by
      ext a
      exact and_congr_right (fun _ => planeAction_eq_one V₂ (inclusion hJN a))
    rw [he]
    exact (Ordinary.planeActor_action_source d eL).2.comap_subtype
  have hXcard : Nat.card ((X.subgroupOf J).map g) = 3 := by
    have he : (X.subgroupOf J).map g = (X.subgroupOf N).map (planeAction V₂) := by
      ext b
      constructor
      · rintro ⟨a,ha,rfl⟩
        exact ⟨inclusion hJN a,ha,rfl⟩
      · rintro ⟨a,ha,rfl⟩
        exact ⟨⟨a.val,(show X ≤ J from le_sup_right) ha⟩,ha,rfl⟩
    rw [he]
    exact (Ordinary.planeActor_action_source d eL).1
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) := hF9.sylow_centralizer.symm.le.trans inf_le_left
  have hQg : Q.subgroupOf J ≤ g.ker := by
    intro a ha
    exact (planeAction_eq_one V₂ (inclusion hJN a)).mpr
      (centralizer_le (d.plane_le_seed.trans d.seed_le)
        (hF9.sylow_centralizer.symm.le ha).2)
  have hQf : ¬ Q.subgroupOf A ≤ f.ker := by
    intro hh
    rw [hfk] at hh
    have hmapped := map_mono (f := A.subtype) hh
    rw [map_subgroupOf_eq_of_le (hQT.trans le_sup_right)] at hmapped
    exact (linear_three_core_escape_of_one_le d hH hF9 hU hV hm hKH hK hL₁K ρ hρ eK hs).2 hmapped
  have hh := symmetricThree_product_quotient_of_local_maps A X hAX f hf hf2 hXA
    g hg hXg hXcard Q (isPGroup_pCoreIn 2 _) hQg hQf
  change Nonempty ((J ⧸ pCore 2 J) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) at hh
  rwa [hJM] at hh

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeC3Local
