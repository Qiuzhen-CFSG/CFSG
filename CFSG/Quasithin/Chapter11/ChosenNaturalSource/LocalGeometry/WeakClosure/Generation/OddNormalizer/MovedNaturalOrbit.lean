module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedRadical
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.FieldFourModule
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# The original natural orbit in the moved J₄ component

The field-four marking kills C_V(L), so the original coordinate projection is
injective. Surjectivity of the residual onto the full L/O₂(L), followed by
SL₃ transitivity on nonzero vectors, constructs conjugators in the original
residual for every pair of nonidentity elements of V.

Central projection through the actual component embedding kills only vectors
centralizing the residual. The covering identity and trivial action of O₂(L)
then put such a vector in C_V(L), so the projection is injective on V itself.
Consequently the literal projected module has order 64 and its residual acts
transitively on its 63 nonidentity elements. Under the actual J₄ marking these
all belong to one of the two native involution classes.

These are additional constraints on the original moved-inner configuration;
they do not assert a classification of all elementary subgroups of J₄.
Source connects them to the odd-normalizer failure and literal Hall kernel.
The remaining local placement and exclusion stay with this task.
Source: Aschbacher--Smith 4.4.5--12, printed pp.620--622, and the natural
chosen-module hypothesis in 11.0.2--3, printed pp.759--760.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The full original residual is transitive on the nonidentity elements of V. -/
theorem odd_residual_module_transitive
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hf : S.field.degree = 2) (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (v w : V) (hv : v ≠ 1) (hw : w ≠ 1) :
    ∃ g ∈ oddActorResidual L A, g * (v : G) * g⁻¹ = (w : G) := by
  obtain ⟨m⟩ := linear_marking_of_field_four D S hf e
  let c : Coordinates D S.field := .sl3 m
  have hi : Function.Injective c.projection := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    exact mem_bot.mp ((original_module_card_of_field_four D S hf e).1 ▸
      (show (x : G) ∈ V ⊓ centralizer (L : Set G) from
        ⟨x.property,(c.projection_eq_one_iff x).mp hx⟩))
  have hv0 : (c.projection v).toAdd ≠ 0 := by
    intro h
    apply hv
    apply hi
    exact (show c.projection v = 1 from congrArg Multiplicative.ofAdd h).trans
      (map_one c.projection).symm
  have hw0 : (c.projection w).toAdd ≠ 0 := by
    intro h
    apply hw
    apply hi
    exact (show c.projection w = 1 from congrArg Multiplicative.ofAdd h).trans
      (map_one c.projection).symm
  obtain ⟨a,ha⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three
    (c.projection v).toAdd (c.projection w).toAdd hv0 hw0
  obtain ⟨b,hb⟩ := actor_cover_quotient D S hA hodd
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (pCore 2 (oddActorResidual L A))
    (b.symm (m.groupEquiv.symm a))
  let l := inclusion ((oddActorResidual_le L A).trans inf_le_left) g
  have hl : c.quotientMap l = a := by
    change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = a
    rw [←hb g,hg,b.apply_symm_apply,m.groupEquiv.apply_symm_apply]
  have hact := c.projection_component_conjugation l v
  rw [hl] at hact
  have he : V.normalizerMonoidHom (inclusion D.normalizes l) v = w := by
    apply hi
    apply Multiplicative.toAdd.injective
    exact hact.trans ha
  exact ⟨g,g.property,congrArg Subtype.val he⟩

/-- The actual central projection is injective on the unchanged module. -/
theorem moved_module_projection_injective
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hf : S.field.degree = 2) (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) :
    Function.Injective ((QuotientGroup.mk' (center K)).subgroupMap
      (movedComponentSubgroup A V K)) := by
  let E := movedComponentSubgroup A V K
  let q := QuotientGroup.mk' (center K)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro v hv
  have hz : (v : K) ∈ center K := (QuotientGroup.eq_one_iff (v : K)).mp
    (congrArg Subtype.val (show q.subgroupMap E v = 1 from hv))
  have hvc : (v.val.val.val : G) ∈ centralizer (oddActorResidual L A : Set G) := by
    intro g hg
    obtain ⟨k,hk,hkg⟩ := hFK hg
    have ht := congrArg (fun x : K => (x.val.val : G)) (mem_center_iff.mp hz ⟨k,hk⟩)
    change (k : G) * (v.val.val.val : G) = (v.val.val.val : G) * (k : G) at ht
    change (k : G) = g at hkg
    simpa only [hkg] using ht
  have hvq : (v.val.val.val : G) ∈ centralizer (L.pCoreIn 2 : Set G) :=
    le_centralizer_iff.mp ((centralizer_eq_core D S).ge.trans inf_le_right) v.property
  have hvL : (v.val.val.val : G) ∈ centralizer (L : Set G) := by
    intro l hl
    obtain ⟨b,hb,r,hr,rfl⟩ := (actor_cover D S hA hodd).1 ▸ hl
    calc
      b * r * (v.val.val.val : G) = b * ((v.val.val.val : G) * r) := by
        rw [mul_assoc,hvq r hr]
      _ = (v.val.val.val : G) * (b * r) := by rw [←mul_assoc,hvc b hb,mul_assoc]
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact mem_bot.mp ((original_module_card_of_field_four D S hf e).1 ▸
    (show (v.val.val.val : G) ∈ V ⊓ centralizer (L : Set G) from ⟨v.property,hvL⟩))

/-- The image of the original V, rather than only a quotient of V, has order 64. -/
theorem moved_projected_module_card
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hf : S.field.degree = 2) (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) :
    Nat.card ((movedComponentSubgroup A V K).map (QuotientGroup.mk' (center K))) = 64 := by
  have hVK : V ≤ K.map (normalizer (A : Set G)).subtype :=
    ((actor_cover D S hA hodd).2.2.1.trans (pCoreIn_le 2 _)).trans hFK
  have hVK' : V.subgroupOf (normalizer (A : Set G)) ≤ K := by
    intro v hv
    obtain ⟨k,hk,he⟩ := hVK hv
    exact (Subtype.ext he : k = v) ▸ hk
  let a : movedComponentSubgroup A V K ≃* V :=
    (subgroupOfEquivOfLe hVK').trans (subgroupOfEquivOfLe (hVK.trans (map_subtype_le _)))
  let f := (QuotientGroup.mk' (center K)).subgroupMap (movedComponentSubgroup A V K)
  let b := MulEquiv.ofBijective f ⟨moved_module_projection_injective D S hA hodd K hFK hf e,
    (QuotientGroup.mk' (center K)).subgroupMap_surjective _⟩
  exact (Nat.card_congr b.toEquiv).symm.trans
    ((Nat.card_congr a.toEquiv).trans (original_module_card_of_field_four D S hf e).2)

/-- The same projected residual conjugates any two nonidentity points of the
literal projected module. No abstract copy of the module is substituted. -/
theorem moved_projected_module_transitive
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hf : S.field.degree = 2) (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier)) :
    let q := QuotientGroup.mk' (center K)
    let X := (movedComponentSubgroup A (oddActorResidual L A) K).map q
    let U := (movedComponentSubgroup A V K).map q
    ∀ u ∈ U, ∀ v ∈ U, u ≠ 1 → v ≠ 1 → ∃ x ∈ X, x * u * x⁻¹ = v := by
  let q := QuotientGroup.mk' (center K)
  dsimp only
  rintro u ⟨a,ha,rfl⟩ v ⟨b,hb,rfl⟩ hu hv
  have ha1 : (⟨a.val.val,ha⟩ : V) ≠ 1 := by
    intro he
    have ha0 : a = 1 := Subtype.ext (Subtype.ext (congrArg (fun z : V => (z : G)) he))
    exact hu (ha0 ▸ map_one q)
  have hb1 : (⟨b.val.val,hb⟩ : V) ≠ 1 := by
    intro he
    have hb0 : b = 1 := Subtype.ext (Subtype.ext (congrArg (fun z : V => (z : G)) he))
    exact hv (hb0 ▸ map_one q)
  obtain ⟨g,hg,he⟩ := odd_residual_module_transitive D S hA hodd hf e
    ⟨a.val.val,ha⟩ ⟨b.val.val,hb⟩ ha1 hb1
  obtain ⟨k,hk,hkg⟩ := hFK hg
  change (k : G) = g at hkg
  let x : K := ⟨k,hk⟩
  have hx : x ∈ movedComponentSubgroup A (oddActorResidual L A) K := by
    change (k : G) ∈ oddActorResidual L A
    rwa [hkg]
  refine ⟨q x,mem_map_of_mem q hx,?_⟩
  have hact : x * a * x⁻¹ = b := by
    apply Subtype.ext
    apply Subtype.ext
    change (k : G) * (a.val.val : G) * (k : G)⁻¹ = (b.val.val : G)
    simpa only [hkg] using he
  simpa only [map_mul,map_inv] using congrArg q hact

/-- After the same J₄ marking, the original elementary 64 has just one
ambient involution class. The conjugators already lie in the residual image. -/
theorem moved_janko_module_pure
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hFK : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype)
    (hf : S.field.degree = 2) (e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier))
    (ek : (K ⧸ center K) ≃* Janko4.Model) :
    let q := QuotientGroup.mk' (center K)
    let X := ((movedComponentSubgroup A (oddActorResidual L A) K).map q).map ek.toMonoidHom
    let U := ((movedComponentSubgroup A V K).map q).map ek.toMonoidHom
    IsElementaryAbelian 2 U ∧ Nat.card U = 64 ∧
      (∀ u ∈ U, ∀ v ∈ U, u ≠ 1 → v ≠ 1 → ∃ x ∈ X, x * u * x⁻¹ = v) ∧
      ((∀ u ∈ U, u ≠ 1 → IsConj Janko4.a u) ∨
        (∀ u ∈ U, u ≠ 1 → IsConj ((Janko4.a * Janko4.b * Janko4.a *
          Janko4.b * Janko4.b) ^ 5) u)) := by
  let q := QuotientGroup.mk' (center K)
  let X := ((movedComponentSubgroup A (oddActorResidual L A) K).map q).map ek.toMonoidHom
  let U := ((movedComponentSubgroup A V K).map q).map ek.toMonoidHom
  have hE := (moved_projected_module D S hA hodd K hFK).1
  let := hE
  have hEU : IsElementaryAbelian 2 U := IsElementaryAbelian.map ek.toMonoidHom
  have hcard : Nat.card U = 64 := by
    rw [card_map_of_injective ek.injective]
    exact moved_projected_module_card D S hA hodd K hFK hf e
  have ht : ∀ u ∈ U, ∀ v ∈ U, u ≠ 1 → v ≠ 1 → ∃ x ∈ X, x * u * x⁻¹ = v := by
    rintro u ⟨u,hu,rfl⟩ v ⟨v,hv,rfl⟩ hu1 hv1
    have hu0 : u ≠ 1 := fun he => hu1 (he ▸ map_one ek)
    have hv0 : v ≠ 1 := fun he => hv1 (he ▸ map_one ek)
    obtain ⟨x,hx,he⟩ := moved_projected_module_transitive D S hA hodd K hFK hf e
      u hu v hv hu0 hv0
    exact ⟨ek x,mem_map_of_mem _ hx,by simpa only [map_mul,map_inv,MulEquiv.coe_toMonoidHom] using congrArg ek he⟩
  refine ⟨hEU,hcard,ht,?_⟩
  let := hEU
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' 2
    (show 2 ∣ Nat.card U by rw [hcard]; decide)
  let u : Janko4.Model := z
  have hu : u ∈ U := z.property
  have hu2 : orderOf u = 2 := (Subgroup.orderOf_coe z).trans hz
  have hu1 : u ≠ 1 := by intro he; rw [he,orderOf_one] at hu2; omega
  have hall (z : Janko4.Model) (hz : IsConj z u) : ∀ v ∈ U, v ≠ 1 → IsConj z v := by
    intro v hv hv1
    obtain ⟨x,_,he⟩ := ht u hu v hv hu1 hv1
    exact hz.trans (isConj_iff.mpr ⟨x,he⟩)
  rcases Janko4.OuterReduction.involution_isConj_of_max1_odd_index
    Janko4.OuterReduction.max1_odd_index_unconditional hu2 with ha | hb
  · exact Or.inl (hall _ ha)
  · exact Or.inr (hall _ hb)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
