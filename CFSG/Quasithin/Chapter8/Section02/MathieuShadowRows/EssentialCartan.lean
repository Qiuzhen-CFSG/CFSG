module
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.SingleBorel
public import CFSG.Quasithin.Chapter3.Section01.ChiefAction.PairedBorel
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.EssentialChiefActor
import all CFSG.Quasithin.Chapter3.Section01.ChiefAction.PairedBorel

/-!
# Split Cartans moving the original essential seed

The single and paired natural branches of B.6.9 supply a component coordinate
that is nonzero on the original essential seed. Conjugating the standard
diagonal torus to the prescribed component Sylow normalizer constructs a
cyclic Cartan in the literal image of H ∩ M. Every nonidentity element moves
that seed, since both eigenvalues of its natural action differ from one.

The original preimage in H ∩ M surjects onto this Cartan with exactly the
original action kernel. Any lift centralizing V lies in that kernel. This
uses no residual-centralization hypothesis and does not assume a complement
or an order-preserving lift. Field reduction, cubic lifting and counting,
and the symmetric-five exclusions remain subsequent steps of the sieve.

Source: Aschbacher--Smith, proof of 3.1.9(6), printed pp.577--578,
refs/quasithin.pdf. The literal M22-code application is M22CodeCartan in
Chapter12/Section02/ReductionSource/NonFFSourceMathieuShadowRows.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter3 ChapterB QuasisimpleSource HigherFieldBorelFixedSpaces

private theorem natural_cartan {E W F : Type*} [Group E] [Finite E]
    [AddCommGroup W] [Module (ZMod 2) W]
    [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (P : Sylow 2 E) (ρ : Representation (ZMod 2) E W) (e : E ≃* SL(2,F))
    (f : W →ₗ[ZMod 2] (Fin 2 → F))
    (hf : ∀ g w, f (ρ g w) = binaryNatural 2 (e g) (f w)) :
    ∃ t : Fˣ →* E, Function.Injective t ∧
      t.range ≤ normalizer (P : Set E) ∧
      ∀ a w, ρ (t a) w = w → f w ≠ 0 → a = 1 := by
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(2,F) Q (upperUnipotentSylow F 2)
  let c : E ≃* SL(2,F) := e.trans (MulAut.conj g)
  have hP : (P : Subgroup E).map c.toMonoidHom = upperUnipotent F := by
    rw [show c.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom from rfl,
      ← Subgroup.map_map]
    exact congrArg Sylow.toSubgroup hg
  let δ : Fˣ →* SL(2,F) := (rankOneBorel F).subtype.comp (borelDiagonalHom (F := F))
  have hδ : Function.Injective δ := by
    intro a b hab
    apply Units.ext
    exact congrArg (fun z : SL(2,F) => z.val 0 0) hab
  let t := c.symm.toMonoidHom.comp δ
  refine ⟨t,c.symm.injective.comp hδ,?_,?_⟩
  · rintro _ ⟨a,rfl⟩
    have hm : c (t a) ∈ normalizer ((P : Subgroup E).map c.toMonoidHom : Set SL(2,F)) := by
      rw [hP]
      change c (c.symm (δ a)) ∈ rankOneBorel F
      rw [c.apply_symm_apply]
      exact (borelDiagonalHom a).property
    rw [← map_equiv_normalizer_eq (P : Subgroup E) c] at hm
    simpa only [c.symm_apply_apply, Sylow.coe_coe] using (Subgroup.mem_map_equiv (f := c)).mp hm
  · intro a w hw hfw
    by_contra ha
    have ha' : (a : F) ≠ 1 := fun he => ha (Units.ext he)
    have he : e (t a) = g⁻¹ * δ a * g := by
      change e (e.symm ((MulAut.conj g).symm (δ a))) = _
      simp
    have hz : binaryNatural (F := F) 2 (δ a) (binaryNatural 2 g (f w)) =
        binaryNatural 2 g (f w) := by
      have hh := congrArg (binaryNatural (F := F) 2 g) ((hf (t a) w).symm.trans (congrArg f hw))
      rw [he] at hh
      simpa only [← Module.End.mul_apply, ← map_mul, mul_assoc, mul_inv_cancel_left] using hh
    have hz' : binaryNatural (F := F) 2 g (f w) = 0 :=
      diagonal_two_fixed_eq_zero a ha' _ hz
    apply hfw
    have hh := congrArg (binaryNatural (F := F) 2 g⁻¹) hz'
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, map_zero] using hh

variable {G D W : Type*} [Group G] [Finite G] [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W]
  {T : Sylow 2 G} {M M₀ H V : Subgroup G}

/-- The split Cartan is contained in the literal image of the source overlap.
Its nonidentity elements move the original seed. -/
theorem source_component_cartan
    (h : QrcHypotheses T M M₀ H V)
    (hP : IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W)
    {L : Subgroup D} (hL : IsComponent D L) [IsSimpleGroup L]
    (heven : 2 ∣ Nat.card L) (F : BinaryField)
    (e : L ≃* SL(2,F.Carrier)) (f : W →ₗ[ZMod 2] (Fin 2 → F.Carrier))
    (hf : ∀ (g : L) w, f (ρ (g : D) w) = binaryNatural 2 (e g) (f w))
    (v : W) (hv : f v ≠ 0) :
    ∃ t : F.Carrierˣ →* D, Function.Injective t ∧
      t.range ≤ ((H ⊓ M).subgroupOf H).map q ∧
      t.range ≤ L ⊓ normalizer
        ((((T.subtype h.right_mem.1.1.2).mapSurjective hq : Sylow 2 D) : Subgroup D) ⊓ L : Set D) ∧
      ∀ a, ρ (t a) v = v → a = 1 := by
  let S := (T.subtype h.right_mem.1.1.2).mapSurjective hq
  obtain ⟨P,hPS⟩ := S.exists_subgroupOf_eq_of_subnormal L hL.1
  obtain ⟨t,ht,htP,htv⟩ := natural_cartan P (ρ.comp L.subtype) e f hf
  let t' := L.subtype.comp t
  have hloc : t'.range ≤ L ⊓ normalizer ((S : Subgroup D) ⊓ L : Set D) := by
    refine le_inf (by rintro _ ⟨a,rfl⟩; exact (t a).property) ?_
    have he : (P : Subgroup L).map L.subtype = (S : Subgroup D) ⊓ L := by
      rw [hPS]
      rw [← inf_subgroupOf_right (S : Subgroup D) L,
        map_subgroupOf_eq_of_le (inf_le_right : (S : Subgroup D) ⊓ L ≤ L)]
    rintro _ ⟨a,rfl⟩
    change t' a ∈ normalizer (((S : Subgroup D) ⊓ L : Subgroup D) : Set D)
    rw [←he]
    exact (P : Subgroup L).le_normalizer_map L.subtype (mem_map_of_mem _ (htP ⟨a,rfl⟩))
  have hmax : ((H ⊓ M).subgroupOf H).map q =
      minimalParabolicMax S (minimalParabolic_reduced_image _ hP q hq hc hn).2 := by
    rw [←h.intrinsic_maximal_eq_intersection hP]
    exact minimalParabolicMax_map_core _ hP q hq
      (minimalParabolic_reduced_image _ hP q hq hc hn).1
  refine ⟨t',L.subtype_injective.comp ht,?_,hloc,fun a ha => htv a v ha hv⟩
  rw [hmax]
  exact hloc.trans (component_sylow_normalizer_le_maximal S
    (minimalParabolic_reduced_image _ hP q hq hc hn).2 hL heven)

/-- A higher-field component with a nonzero coordinate of the original seed. -/
structure SeedCartan (q : H →* D) (ρ : Representation (ZMod 2) D W) (v : W) where
  field : BinaryField
  large : 4 ≤ Nat.card field.Carrier
  embedding : field.Carrierˣ →* D
  injective : Function.Injective embedding
  in_overlap : embedding.range ≤ ((H ⊓ M).subgroupOf H).map q
  seed_free : ∀ a, ρ (embedding a) v = v → a = 1
  component : Subgroup D
  component_isComponent : IsComponent D component
  component_equiv : component ≃* SL(2,field.Carrier)
  in_component : embedding.range ≤ component
  coordinate : W →ₗ[ZMod 2] (Fin 2 → field.Carrier)
  coordinate_natural : ∀ (g : component) w,
    coordinate (ρ (g : D) w) = binaryNatural 2 (component_equiv g) (coordinate w)
  coordinate_seed : coordinate v ≠ 0

/-- The single natural branch constructs its Cartan from the actual component. -/
theorem single_seed_cartan
    (h : QrcHypotheses T M M₀ H V)
    (hP : IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W) (hfaith : Function.Injective ρ) (hi : IsIrreducible ρ)
    (v : W) (hv : v ≠ 0)
    (hqs : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (s : MovedSection (ρ.comp (offenderSubgroup ρ).subtype)
      (generalizedFitting (offenderSubgroup ρ)))
    (F : BinaryField)
    (e : ActionEquiv (s.action.comp (generalizedFitting (offenderSubgroup ρ)).subtype)
      (linearNatural F 2)) :
    Nonempty (SeedCartan (M := M) q ρ v) := by
  let Y := offenderSubgroup ρ
  let A := generalizedFitting Y
  let : Y.Normal := offenderSubgroup_normal ρ
  let : IsQuasisimple A := hqs
  let eA := A.equivMapOfInjective Y.subtype Y.subtype_injective
  let eL := eA.symm.trans e.groupEquiv
  have hF := quasisimple_linear_two_card_ge_four F e.groupEquiv
  obtain ⟨hs,hL,heven⟩ := Chapter3.naturalFactor_structure Y A F hF e.groupEquiv
  let := hs
  let : IsSimpleGroup A := eA.isSimpleGroup
  obtain ⟨f,hfi,hfe⟩ := whole_natural_coordinate_of_moved_section ρ hfaith hi Y A
    (A.nontrivial_iff_ne_bot.mp inferInstance) s F e
  have hfeL (g : A.map Y.subtype) (w : W) :
      f (ρ (g : D) w) = binaryNatural 2 (eL g) (f w) := by
    have he : (((eA.symm g : A) : Y) : D) = (g : D) :=
      congrArg Subtype.val (eA.apply_symm_apply g)
    rw [←he]
    exact hfe (eA.symm g) w
  have hfv : f v ≠ 0 := fun hz => hv (hfi (hz.trans f.map_zero.symm))
  obtain ⟨t,ht,ho,hcomp,hf⟩ := source_component_cartan h hP q hq hc hn ρ hL heven F eL f hfeL v hfv
  exact ⟨⟨F,hF,t,ht,ho,hf,A.map Y.subtype,hL,eL,hcomp.trans inf_le_left,f,hfeL,hfv⟩⟩

/-- Either natural coordinate that contains the seed supplies the same source
Cartan construction, without presuming a faithful quotient lift. -/
theorem paired_seed_cartan
    (h : QrcHypotheses T M M₀ H V)
    (hP : IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W) (hfaith : Function.Injective ρ) (hi : IsIrreducible ρ)
    (v : W) (hv : v ≠ 0)
    (d : SourceInduction.SourceTwoFactorCase (ρ.comp (offenderSubgroup ρ).subtype))
    (F : BinaryField) (hF : 4 ≤ Nat.card F.Carrier)
    (c : d.MarkedProduct (linearNatural F 2)) :
    Nonempty (SeedCartan (M := M) q ρ v) := by
  let Y := offenderSubgroup ρ
  let := offenderSubgroup_normal ρ
  let := d.product.first_normal
  let := d.product.second_normal
  let e₁ := Chapter3.firstEquiv c.action.groupEquiv d.first c.first_eq
  let e₂ := Chapter3.secondEquiv c.action.groupEquiv d.second c.second_eq
  let m₁ := d.first.equivMapOfInjective Y.subtype Y.subtype_injective
  let m₂ := d.second.equivMapOfInjective Y.subtype Y.subtype_injective
  let f := c.action.linearEquiv.toLinearMap.comp (fixed (ρ.comp Y.subtype)).toSubmodule.mkQ
  let f₁ := (LinearMap.fst (ZMod 2) (Fin 2 → F.Carrier) (Fin 2 → F.Carrier)).comp f
  let f₂ := (LinearMap.snd (ZMod 2) (Fin 2 → F.Carrier) (Fin 2 → F.Carrier)).comp f
  have hf : ∀ g : Y, ∀ w, f (ρ (g : D) w) =
      (linearNatural F 2 ((c.action.groupEquiv g).1) ((f w).1),
       linearNatural F 2 ((c.action.groupEquiv g).2) ((f w).2)) := by
    intro g w
    exact (congrArg c.action.linearEquiv
      ((fixed (ρ.comp Y.subtype)).quotientRepresentation_mk g w).symm).trans
        (c.action.intertwines g _)
  have hf₁ : ∀ (g : d.first.map Y.subtype) w,
      f₁ (ρ (g : D) w) = binaryNatural 2 ((m₁.symm.trans e₁) g) (f₁ w) := by
    intro g w
    obtain ⟨a,rfl⟩ := m₁.surjective g
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change (f (ρ (a : Y) w)).1 = linearNatural F 2 (e₁ a) ((f w).1)
    rw [hf]
    rw [show e₁ a = (c.action.groupEquiv a).1 from Chapter3.firstEquiv_apply _ _ _ _]
  have hf₂ : ∀ (g : d.second.map Y.subtype) w,
      f₂ (ρ (g : D) w) = binaryNatural 2 ((m₂.symm.trans e₂) g) (f₂ w) := by
    intro g w
    obtain ⟨a,rfl⟩ := m₂.surjective g
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change (f (ρ (a : Y) w)).2 = linearNatural F 2 (e₂ a) ((f w).2)
    rw [hf]
    rw [show e₂ a = (c.action.groupEquiv a).2 from Chapter3.secondEquiv_apply _ _ _ _]
  obtain ⟨hs₁,hL₁,he₁⟩ := Chapter3.naturalFactor_structure Y d.first F hF e₁
  obtain ⟨hs₂,hL₂,he₂⟩ := Chapter3.naturalFactor_structure Y d.second F hF e₂
  let := hs₁
  let := hs₂
  have hfv : f v ≠ 0 := by
    intro hz
    have hY : Y ≠ ⊥ := by
      let : IsSimpleGroup d.first := m₁.isSimpleGroup
      let : Nontrivial Y := Function.Injective.nontrivial d.first.subtype_injective
      exact (Subgroup.nontrivial_iff_ne_bot Y).mp inferInstance
    have hfix : (fixed (ρ.comp Y.subtype)).toSubmodule = ⊥ :=
      fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hfaith hi Y hY
    have hquot : (fixed (ρ.comp Y.subtype)).toSubmodule.mkQ v = 0 :=
      c.action.linearEquiv.injective (hz.trans c.action.linearEquiv.map_zero.symm)
    have hm : v ∈ (fixed (ρ.comp Y.subtype)).toSubmodule :=
      (Submodule.Quotient.mk_eq_zero _).mp hquot
    exact hv (by simpa only [hfix, Submodule.mem_bot] using hm)
  by_cases hv₁ : f₁ v = 0
  · have hv₂ : f₂ v ≠ 0 := fun hh => hfv (Prod.ext hv₁ hh)
    obtain ⟨t,ht,ho,hcomp,hf⟩ := source_component_cartan h hP q hq hc hn ρ hL₂ he₂ F
      (m₂.symm.trans e₂) f₂ hf₂ v hv₂
    exact ⟨⟨F,hF,t,ht,ho,hf,d.second.map Y.subtype,hL₂,m₂.symm.trans e₂,
      hcomp.trans inf_le_left,f₂,hf₂,hv₂⟩⟩
  · obtain ⟨t,ht,ho,hcomp,hf⟩ := source_component_cartan h hP q hq hc hn ρ hL₁ he₁ F
      (m₁.symm.trans e₁) f₁ hf₁ v hv₁
    exact ⟨⟨F,hF,t,ht,ho,hf,d.first.map Y.subtype,hL₁,m₁.symm.trans e₁,
      hcomp.trans inf_le_left,f₁,hf₁,hv₁⟩⟩

namespace SeedCartan
variable {q : H →* D} {ρ : Representation (ZMod 2) D W} {v : W}
  (c : SeedCartan (M := M) q ρ v)

/-- The full original preimage in H ∩ M; it is not a selected complement. -/
@[expose] def originalPreimage : Subgroup H :=
  ((H ⊓ M).subgroupOf H) ⊓ c.embedding.range.comap q

omit [Finite G] [Finite D] in
/-- The full original preimage surjects onto the split Cartan, retaining its
entire action kernel. Centralizing lifts lie in this kernel. -/
theorem original_preimage_projection
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v) :
    ∃ p : c.originalPreimage →* c.field.Carrierˣ,
      Function.Surjective p ∧
      c.embedding.comp p = q.comp c.originalPreimage.subtype ∧
      p.ker = q.ker.subgroupOf c.originalPreimage ∧
      ∀ x : c.originalPreimage, ((x : H) : G) ∈ centralizer (V : Set G) → p x = 1 := by
  let e := MonoidHom.ofInjective c.injective
  let f : c.originalPreimage →* c.embedding.range :=
    (q.comp c.originalPreimage.subtype).codRestrict _ (fun x => x.property.2)
  let p := e.symm.toMonoidHom.comp f
  have hp : Function.Surjective p := by
    intro a
    obtain ⟨x,hx,hxa⟩ := c.in_overlap (show c.embedding a ∈ c.embedding.range from ⟨a,rfl⟩)
    have hxX : x ∈ c.originalPreimage := ⟨hx,show q x ∈ c.embedding.range from hxa ▸ ⟨a,rfl⟩⟩
    refine ⟨⟨x,hxX⟩,?_⟩
    apply e.injective
    change e (e.symm (f ⟨x,hxX⟩)) = e a
    rw [e.apply_symm_apply]
    exact Subtype.ext hxa
  have he : c.embedding.comp p = q.comp c.originalPreimage.subtype := by
    ext x
    exact congrArg Subtype.val (e.apply_symm_apply (f x))
  have hk : p.ker = q.ker.subgroupOf c.originalPreimage := by
    have hh := congrArg MonoidHom.ker he
    rw [MonoidHom.ker_comp_of_injective _ _ c.injective] at hh
    exact hh
  refine ⟨p,hp,he,hk,?_⟩
  intro x hx
  apply c.seed_free
  have hh := DFunLike.congr_fun he x
  change c.embedding (p x) = q (x : H) at hh
  rw [hh]
  exact hv x hx

omit [Finite G] [Finite D] in
/-- The image of a source subgroup in this Cartan cannot be nontrivial if
that subgroup centralizes the original module. -/
theorem image_eq_bot_of_centralizes
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    (X : Subgroup H) (hX : X.map q ≤ c.embedding.range)
    (hC : X.map H.subtype ≤ centralizer (V : Set G)) : X.map q = ⊥ := by
  apply bot_unique
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨a,ha⟩ := hX (mem_map_of_mem q hx)
  have hvx := hv x (hC (mem_map_of_mem H.subtype hx))
  rw [←ha] at hvx
  have hane := c.seed_free a hvx
  rw [←ha,hane,map_one]
  exact one_mem _

end SeedCartan

omit [Finite G] [Finite D] in
private theorem small_or_cartan_cover
    (q : H →* D) (ρ : Representation (ZMod 2) D W) (v : W)
    (hv : ∀ x : H, (x : G) ∈ centralizer (V : Set G) → ρ (q x) v = v)
    (hs : ChiefSmallNaturalAlternatives ρ ∨ Nonempty (SeedCartan (M := M) q ρ v)) :
    ChiefSmallNaturalAlternatives ρ ∨
      ∃ c : SeedCartan (M := M) q ρ v,
        ∃ p : c.originalPreimage →* c.field.Carrierˣ,
          Function.Surjective p ∧
          c.embedding.comp p = q.comp c.originalPreimage.subtype ∧
          p.ker = q.ker.subgroupOf c.originalPreimage ∧
          ∀ x : c.originalPreimage,
            ((x : H) : G) ∈ centralizer (V : Set G) → p x = 1 := by
  exact hs.elim Or.inl (fun hc => hc.elim
    (fun c => Or.inr ⟨c,c.original_preimage_projection hv⟩))

private theorem natural_small_or_seed_cartan [FiniteDimensional (ZMod 2) W]
    (h : QrcHypotheses T M M₀ H V)
    (hP : IsMinimalParabolicOver (T.subtype h.right_mem.1.1.2) ⊤)
    (q : H →* D) (hq : Function.Surjective q)
    (hc : pCore 2 D = ⊥) (hn : q.ker ≠ ⊤)
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ) (hi : IsIrreducible ρ)
    (v : W) (hv : v ≠ 0) (hns : ¬ Group.IsSolvable D)
    (hp : IsMinimalParabolicOver ((T.subtype h.right_mem.1.1.2).mapSurjective hq) ⊤)
    (hff : IsFFModule ρ) (hnat : ChiefNaturalAlternatives ρ) :
    ChiefSmallNaturalAlternatives ρ ∨ Nonempty (SeedCartan (M := M) q ρ v) := by
  rcases hnat with hsmall | ⟨hqs,c,hm⟩ | ⟨d,hm⟩
  · exact Or.inl (Or.inl hsmall)
  · rcases hm with ⟨F,⟨e⟩⟩ | hs
    · exact Or.inr (single_seed_cartan h hP q hq hc hn ρ hf hi v hv hqs c.sectionData F e)
    · exact Or.inl (Or.inr (Or.inl ⟨hqs,c,hs⟩))
  · rcases hm with ⟨F,⟨e⟩⟩ | hs
    · have hdeg : F.degree ≠ 1 := by
        intro hd
        exact hns (source_pair_degree_one_solvable ρ
          ((T.subtype h.right_mem.1.1.2).mapSurjective hq) hp hff hc d F hd e)
      have hF : 4 ≤ Nat.card F.Carrier := by
        rw [F.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < 2)
          (show 2 ≤ F.degree from by have := F.degree_pos; omega)
      exact Or.inr (paired_seed_cartan h hP q hq hc hn ρ hf hi v hv d F hF e)
    · exact Or.inl (Or.inr (Or.inr ⟨d,hs⟩))

variable [IsElementaryAbelian 2 ((ChapterD.conjugateSpan H V).subgroupOf H)]

set_option backward.isDefEq.respectTransparency false in
/-- The actual nonsolvable essential source action has either a small natural
marking or a split Cartan acting faithfully on the original nonzero seed. -/
theorem essential_small_or_seed_cartan
    (h : QrcHypotheses T M M₀ H V)
    (hD : IsSQTK KnownSimple.IsKnownSimple H) (hns : ¬ Group.IsSolvable H)
    {hVH : V ≤ H}
    (a : EssentialSeedAction H V (T.subtype h.right_mem.1.1.2) hVH)
    (hff : IsFFModule a.imageRepresentation) :
    ChiefSmallNaturalAlternatives a.imageRepresentation ∨
      Nonempty (SeedCartan (M := M) a.projection a.imageRepresentation a.vector) := by
  let := a.irreducible
  have hns' : ¬ Group.IsSolvable a.Actor := fun hs =>
    hns ((chief_image_solvable_iff _ a.original_minimal a.representation hff).mp hs)
  exact natural_small_or_seed_cartan h a.original_minimal a.projection a.projection_surjective
    a.twoCore_eq_bot a.projection_kernel_ne_top a.imageRepresentation
    (imageRepresentation_injective a.representation)
    (imageRepresentation_irreducible a.representation a.irreducible) a.vector
    a.vector_ne_zero hns' a.reduced_minimal hff
    (minimalParabolic_chief_natural_alternatives a.representation hD _
      a.original_minimal hff).1

set_option backward.isDefEq.respectTransparency false in
/-- The actual essential action retains the full source preimage map as well
as the Cartan marking. -/
theorem essential_small_or_seed_cartan_cover
    (h : QrcHypotheses T M M₀ H V)
    (hD : IsSQTK KnownSimple.IsKnownSimple H) (hns : ¬ Group.IsSolvable H)
    {hVH : V ≤ H}
    (a : EssentialSeedAction H V (T.subtype h.right_mem.1.1.2) hVH)
    (hff : IsFFModule a.imageRepresentation) :
    ChiefSmallNaturalAlternatives a.imageRepresentation ∨
      ∃ c : SeedCartan (M := M) a.projection a.imageRepresentation a.vector,
        ∃ p : c.originalPreimage →* c.field.Carrierˣ,
          Function.Surjective p ∧
          c.embedding.comp p = a.projection.comp c.originalPreimage.subtype ∧
          p.ker = a.projection.ker.subgroupOf c.originalPreimage ∧
          ∀ x : c.originalPreimage,
            ((x : H) : G) ∈ centralizer (V : Set G) → p x = 1 := by
  exact small_or_cartan_cover a.projection a.imageRepresentation a.vector
    a.vector_centralizer_fixed (essential_small_or_seed_cartan h hD hns a hff)

end CFSG.Quasithin.Chapter8.MathieuShadowRows
