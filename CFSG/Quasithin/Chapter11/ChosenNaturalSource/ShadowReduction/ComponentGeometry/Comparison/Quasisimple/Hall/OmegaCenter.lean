module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.RankTwoInner
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.Cardinalities
public import Theory.GroupTheory.PGroup.OmegaCenterIn
public import Theory.GroupTheory.CoprimeCentralizerCard

/-!
# The whole radical omega-center and its actual Hall action

Characteristic two identifies Ω₁Z(R₁) with C_VK(R₁), using the original
ambient inclusions. The normalizer of R₁ preserves this whole subgroup.
Its conjugation action factors through the literal VK-action projection,
and a full Sylow subgroup maps onto a full Sylow subgroup of the quotient
normalizer, with exactly the same induced omega-center automorphisms.

The model normalizer calculation gives rank two for every such odd Sylow
actor at primes dividing q−1. This actor lies in the point component, so
it fixes the original nonidentity z. Coprime fixed/moved decomposition
therefore makes its omega-center displacement strictly smaller than the
whole omega-center. If that center equals the original line, the bound is
strictly below q. OmegaCenterComparison applies this to the original
escaping-normalizer alternative with all actor choices discharged.

The opposite lower bound from the marked model action, and hence strict
omega-center containment and final comparison equality, remain with this
comparison owner. No action-order or displacement premise is introduced.
Source: Aschbacher–Smith 11.4.2, printed p.777.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The whole source Z₁, with the center embedded before taking omega. -/
def radicalOmega : Subgroup G := omegaOneAmbient ((center E.R₁).map E.R₁.subtype)

/-- Agreement with the two intrinsic subtype maps. -/
theorem radicalOmega_eq : radicalOmega E = omegaCenterIn E.R₁ :=
  (omegaCenterIn_eq_omegaOneAmbient E.R₁).symm

/-- The whole source center is elementary abelian. -/
instance radicalOmega_elementary : IsElementaryAbelian 2 (radicalOmega E) := by
  rw [radicalOmega_eq]
  infer_instance

/-- Local characteristic two identifies the whole center with the fixed
subgroup of the actual VK module under R₁. -/
theorem radicalOmega_eq_module_centralizer
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G)) :
    radicalOmega E = VK E ⊓ centralizer (E.R₁ : Set G) := by
  rw [radicalOmega_eq, VK_eq_omegaCenter]
  ext x
  simp only [mem_inf,mem_omegaCenterIn_iff,mem_omegaOneCenterAmbient_iff]
  constructor
  · rintro ⟨hxR,hxc,hx2⟩
    have hxH : x ∈ localGroup E := (show (T : Subgroup G) ≤ localGroup E from le_sup_right)
      (radical_le_sylow E hxR)
    have hc : (⟨x,hxH⟩ : localGroup E) ∈ centralizer (pCore 2 (localGroup E) : Set (localGroup E)) := by
      intro q hq
      exact Subtype.ext (hxc q (core_le_radical E (mem_map_of_mem _ hq)))
    exact ⟨⟨mem_map_of_mem _ (local_characteristic E hstar hc),hx2,
      fun q hq => hxc q (core_le_radical E hq)⟩,hxc⟩
  · rintro ⟨⟨hxQ,hx2,_⟩,hxc⟩
    exact ⟨core_le_radical E hxQ,hxc,hx2⟩

/-- Every original radical normalizer preserves its characteristic omega-center. -/
theorem normalizer_le_radicalOmega_normalizer :
    normalizer (E.R₁ : Set G) ≤ normalizer (radicalOmega E : Set G) := by
  rw [radicalOmega_eq]
  exact normalizer_le_normalizer_omegaCenterIn E.R₁

/-- The original line lies in the whole center, without assuming equality. -/
theorem line_le_radicalOmega
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) : E.V₁ ≤ radicalOmega E := by
  rw [radicalOmega_eq_module_centralizer E hstar]
  exact le_inf (line_le_module E hstar hcent) hcent

/-- Every actor in the point component fixes the original nonzero central point. -/
theorem point_mem_radicalOmega_fixed
    (h : EarlierGeometry E) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (Y : Subgroup G) (hYK : Y ≤ E.Kz) :
    E.z ∈ radicalOmega E ⊓ centralizer (Y : Set G) := by
  refine ⟨line_le_radicalOmega E hstar hcent h.point_mem,?_⟩
  intro y hy
  exact mem_centralizer_singleton_iff.mp (h.point_component.1 (hYK hy))

/-- Coprime splitting retains a nontrivial fixed factor, so the displacement
under any original point-fixed odd actor is strictly smaller. -/
theorem radicalOmega_moved_card_lt
    (h : EarlierGeometry E) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (Y : Subgroup G) (hYK : Y ≤ E.Kz) (hYR : Y ≤ normalizer (E.R₁ : Set G))
    (hY : IsPGroup p Y) :
    Nat.card (⁅radicalOmega E,Y⁆ : Subgroup G) < Nat.card (radicalOmega E) := by
  have hn := hYR.trans (normalizer_le_radicalOmega_normalizer E)
  have hc : Nat.Coprime (Nat.card Y) (Nat.card (radicalOmega E)) :=
    IsPGroup.coprime_card_of_ne p 2 (by rintro rfl; obtain ⟨k,hk⟩ := hp; omega) Y (radicalOmega E) hY
      (IsElementaryAbelian.isPGroup 2 (radicalOmega E))
  have hprod := commutator_card_mul_centralizer_card (radicalOmega E) Y hn hc
  have hne : radicalOmega E ⊓ centralizer (Y : Set G) ≠ ⊥ := by
    intro he
    exact h.point_ne_one (he.le (point_mem_radicalOmega_fixed E h hstar hcent Y hYK))
  have htwo : 1 < Nat.card (radicalOmega E ⊓ centralizer (Y : Set G) : Subgroup G) :=
    (one_lt_card_iff_ne_bot _).mpr hne
  have hpos : 0 < Nat.card (⁅radicalOmega E,Y⁆ : Subgroup G) := Nat.card_pos
  nlinarith

/-- The map on the literal radical normalizers is the original action projection. -/
def radicalNormalizerProjection :
    normalizer (radical E : Set (localGroup E)) →*
      normalizer ((radical E).map (projection E) : Set (ActionQuotient E)) :=
  ((projection E).comp (normalizer (radical E : Set (localGroup E))).subtype).codRestrict _
    (fun g => (radical E).le_normalizer_map (projection E) (mem_map_of_mem _ g.property))

@[simp] theorem radicalNormalizerProjection_apply
    (g : normalizer (radical E : Set (localGroup E))) :
    (radicalNormalizerProjection E g).val = projection E g.val := rfl

/-- Relative Sylow lifting makes the literal normalizer projection surjective. -/
theorem radicalNormalizerProjection_surjective
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) :
    Function.Surjective (radicalNormalizerProjection E) := by
  intro g
  have hg : g.val ∈ (normalizer (radical E : Set (localGroup E))).map (projection E) := by
    rw [radical_normalizer_image E h hf hne hstar hcent]
    exact g.property
  obtain ⟨x,hx,he⟩ := hg
  exact ⟨⟨x,hx⟩,Subtype.ext he⟩

/-- The actual ambient subgroup obtained from a Sylow subgroup of N_KzT(R₁). -/
def radicalSylowActor (p : ℕ)
    (P : Sylow p (normalizer (radical E : Set (localGroup E)))) : Subgroup G :=
  ((P : Subgroup (normalizer (radical E : Set (localGroup E)))).map
    (normalizer (radical E : Set (localGroup E))).subtype).map (localGroup E).subtype

/-- Every full Sylow choice gives an actual point-fixed rank-two actor,
retaining its original normalizer inclusion and prime. -/
theorem radicalSylowActor_properties
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) (hm : RankTwoModel E)
    (hinner : (radical E).map (projection E) ≤ (component E).map (projection E))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hd : p ∣ 2^E.input.field.degree - 1)
    (P : Sylow p (normalizer (radical E : Set (localGroup E)))) :
    radicalSylowActor E p P ≤ E.Kz ∧
      radicalSylowActor E p P ≤ normalizer (E.R₁ : Set G) ∧
      IsPGroup p (radicalSylowActor E p P) ∧
      2 ≤ primeRank p (radicalSylowActor E p P) := by
  let N := normalizer (radical E : Set (localGroup E))
  let A := (P : Subgroup N).map N.subtype
  have hA : IsPGroup p A := P.isPGroup'.map _
  refine ⟨?_,?_,hA.map _,?_⟩
  · rintro _ ⟨a,ha,rfl⟩
    exact odd_subgroup_le_component E h hp A hA ha
  · have hR : E.R₁ ≤ localGroup E := (radical_le_sylow E).trans le_sup_right
    have he : N.map (localGroup E).subtype = normalizer (E.R₁ : Set G) ⊓ localGroup E := by
      change (normalizer (E.R₁.subgroupOf (localGroup E) : Set (localGroup E))).map (localGroup E).subtype = _
      rw [←subgroupOf_normalizer_eq hR,subgroupOf_map_subtype]
    exact (map_mono (map_subtype_le (P : Subgroup N))).trans (he.le.trans inf_le_left)
  · obtain ⟨Q,hQ⟩ := exists_model_normalizer_of_inner_radical E h hf hne hstar hcent hm hinner
    have hr := radical_image_normalizer_rank_of_model E hm Q hQ hp hd
    have hsur := radicalNormalizerProjection_surjective E h hf hne hstar hcent
    have hrN := two_le_primeRank_of_image hp (radicalNormalizerProjection E) (by
      rwa [MonoidHom.range_eq_top.mpr hsur,primeRank_equiv p topEquiv])
    change 2 ≤ primeRank p (A.map (localGroup E).subtype)
    rw [←primeRank_equiv p (A.equivMapOfInjective (localGroup E).subtype Subtype.val_injective),
      ←primeRank_equiv p ((P : Subgroup N).equivMapOfInjective N.subtype Subtype.val_injective),
      ←P.primeRank_eq]
    exact hrN

/-- The Sylow image is a full Sylow subgroup of the actual quotient normalizer. -/
def radicalImageSylow
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) {p : ℕ} [Fact p.Prime]
    (P : Sylow p (normalizer (radical E : Set (localGroup E)))) :
    Sylow p (normalizer ((radical E).map (projection E) : Set (ActionQuotient E))) :=
  P.mapSurjective (f := radicalNormalizerProjection E)
    (radicalNormalizerProjection_surjective E h hf hne hstar hcent)

/-- Intrinsic normalizer membership retains the same ambient element. -/
theorem radicalNormalizer_mem_ambient
    (g : normalizer (radical E : Set (localGroup E))) :
    (g.val : G) ∈ normalizer (E.R₁ : Set G) := by
  have hg := g.property
  change g.val ∈ normalizer (E.R₁.subgroupOf (localGroup E) : Set (localGroup E)) at hg
  have hR : E.R₁ ≤ localGroup E := (radical_le_sylow E).trans le_sup_right
  rw [←subgroupOf_normalizer_eq hR] at hg
  exact hg

/-- Conjugation on the entire omega-center, through the original inclusions. -/
def radicalOmegaLocalAction :
    normalizer (radical E : Set (localGroup E)) →* MulAut (radicalOmega E) :=
  (radicalOmega E).normalizerMonoidHom.comp
    (((localGroup E).subtype.comp (normalizer (radical E : Set (localGroup E))).subtype).codRestrict _
      (fun g => normalizer_le_radicalOmega_normalizer E (radicalNormalizer_mem_ambient E g)))

@[simp] theorem radicalOmegaLocalAction_apply
    (g : normalizer (radical E : Set (localGroup E))) (v : radicalOmega E) :
    (radicalOmegaLocalAction E g v).val = (g.val : G) * v.val * (g.val : G)⁻¹ := rfl

/-- The original VK-kernel also centralizes the whole omega-center of R₁. -/
theorem radicalOmegaLocalAction_kills_kernel
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G)) :
    (radicalNormalizerProjection E).ker ≤ (radicalOmegaLocalAction E).ker := by
  intro g hg
  have hg' : projection E g.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
  have hc : g.val ∈ centralizer (moduleSubgroup E : Set (localGroup E)) :=
    (QuotientGroup.eq_one_iff _).mp hg'
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  rw [radicalOmegaLocalAction_apply]
  obtain ⟨w,hw,he⟩ := (radicalOmega_eq_module_centralizer E hstar).le v.property |>.1
  have hh := congrArg (localGroup E).subtype (hc w hw)
  change (w : G) * (g.val : G) = (g.val : G) * (w : G) at hh
  change (g.val : G) * v.val * (g.val : G)⁻¹ = v.val
  change (w : G) = v.val at he
  rw [←he,←hh,mul_inv_cancel_right]

/-- The quotient-normalizer action is constructed, rather than supplied as an input. -/
def radicalOmegaImageAction
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) :
    normalizer ((radical E).map (projection E) : Set (ActionQuotient E)) →*
      MulAut (radicalOmega E) :=
  (radicalNormalizerProjection E).liftOfSurjective
    (radicalNormalizerProjection_surjective E h hf hne hstar hcent)
    ⟨radicalOmegaLocalAction E,radicalOmegaLocalAction_kills_kernel E hstar⟩

/-- The quotient action keeps the literal conjugation convention. -/
theorem radicalOmegaImageAction_projection
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    (g : normalizer (radical E : Set (localGroup E))) :
    radicalOmegaImageAction E h hf hne hstar hcent (radicalNormalizerProjection E g) =
      radicalOmegaLocalAction E g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

/-- Full Sylow image and ambient Sylow actor induce precisely the same
omega-center automorphisms. -/
theorem radicalImageSylow_action_image
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) {p : ℕ} [Fact p.Prime]
    (P : Sylow p (normalizer (radical E : Set (localGroup E)))) :
    ((radicalImageSylow E h hf hne hstar hcent P : Sylow p _ ) : Subgroup _).map
        (radicalOmegaImageAction E h hf hne hstar hcent) =
      (P : Subgroup _).map (radicalOmegaLocalAction E) := by
  change ((P : Subgroup _).map (radicalNormalizerProjection E)).map _ = _
  rw [map_map]
  congr 1
  apply MonoidHom.ext
  intro g
  exact radicalOmegaImageAction_projection E h hf hne hstar hcent g

variable {E}

/-- The original flag line has exactly the original field cardinality. -/
theorem ofFlag_line_card
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) :
    Nat.card (ofFlag S f X z H).V₁ = 2^S.field.degree := by
  change Nat.card (c.preimage (f.space 0)) = _
  rw [Closure.Nonabelian.card_preimage c hf, f.dimension 0]
  exact pow_one _

/-- Under omega-center equality the actual point-fixed odd actor has a
strictly smaller moved subgroup than the original field line. -/
theorem ofFlag_radicalOmega_moved_card_lt_field
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hZ : (ofFlag S f X z H).V₁ = radicalOmega (ofFlag S f X z H))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (Y : Subgroup G) (hYK : Y ≤ (ofFlag S f X z H).Kz)
    (hYR : Y ≤ normalizer ((ofFlag S f X z H).R₁ : Set G)) (hY : IsPGroup p Y) :
    Nat.card (⁅radicalOmega (ofFlag S f X z H),Y⁆ : Subgroup G) < 2^S.field.degree := by
  have hh := radicalOmega_moved_card_lt (ofFlag S f X z H) h hstar hcent hp Y hYK hYR hY
  have hc : Nat.card (radicalOmega (ofFlag S f X z H)) = 2^S.field.degree := by
    rw [←hZ,ofFlag_line_card S f X z H hf]
  exact hh.trans_eq hc
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
