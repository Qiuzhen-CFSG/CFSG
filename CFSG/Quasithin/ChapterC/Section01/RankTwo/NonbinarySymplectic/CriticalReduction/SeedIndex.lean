module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StarEscape
public import Theory.Representation.SymplecticFourOrthogonalCover.SylowSeedIndex

/-!
# The normalized Sylow seed has small elementary action

For every replacement vertex, an elementary actor normalizing its full Sylow
seed acts on that seed through field automorphisms. The exact centralizer
index is therefore at most the original field degree. This retains the
entire central attachment and needs no quadraticity on the vertex layer.

Source: MS93 (3.4), p.868; the application is the full endpoint intersection
in the first star comparison.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
section Model
variable {M J V F : Type*} [Group M] [Finite M] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  {ρ₀ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
  {R : Subgroup M} {u : Vertex R}

private theorem elementary_seed_actor_index_le_ringAut
    (hFl : 2 < Nat.card F) (s : MovedSection ρ₀ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (he : IsCover (MovedSection.coverProjection s e))
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R)
    (hj : Function.Injective j) (hjr : j.range = U R u)
    (κ : stabilizer R u →* J)
    (hκL : ((Ltilde R u).subgroupOf (stabilizer R u)).map κ = B)
    (hcent : centralizer (B : Set J) = ⊥)
    (hsemi : ∀ g, ∃ σ : F ≃+* F, ∀ c v,
      MovedSection.ambientAction s e g (c • v) = σ c • MovedSection.ambientAction s e g v)
    (hconj : ∀ (g : stabilizer R u) (w : s.space.toSubmodule),
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ g) w)) =
        (g : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (g : FreeAmalgam R)⁻¹)
    (P : Sylow 2 (Ltilde R u)) (A : Subgroup (FreeAmalgam R))
    (hA : A ≤ stabilizer R u)
    (hn : A ≤ normalizer (componentSylowSeed R u P : Set (FreeAmalgam R)))
    (hsquare : ∀ a ∈ A, a*a=1) :
    (centralizer (componentSylowSeed R u P : Set (FreeAmalgam R))).relIndex A ≤
      Nat.card (F ≃+* F) := by
  let σ := MovedSection.coverAction s e
  let ψ := MovedSection.ambientAction s e
  let ρ := s.space.toRepresentation
  let p := MovedSection.coverProjection s e
  let δ := κ.comp (inclusion hA)
  have hδ (x : A) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (ρ (δ x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹ :=
    hconj (inclusion hA x) w
  let f₀ : Ltilde R u →* J :=
    κ.comp (inclusion (Ltilde_le_stabilizer u))
  have hf₀ : f₀.range = B := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact hκL
  let f := e.groupEquiv.toMonoidHom.comp (f₀.codRestrict B (fun x => hf₀ ▸ ⟨x,rfl⟩))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨y,hy⟩ := (show (e.groupEquiv.symm x : J) ∈ f₀.range from
      hf₀.symm ▸ (e.groupEquiv.symm x).property)
    refine ⟨y,?_⟩
    change e.groupEquiv ⟨f₀ y,_⟩ = x
    rw [show (⟨f₀ y,_⟩ : B) = e.groupEquiv.symm x from Subtype.ext hy,
      e.groupEquiv.apply_symm_apply]
  have hfmark (x : Ltilde R u) :
      (e.groupEquiv.symm (f x) : J) = f₀ x := by
    change (e.groupEquiv.symm (e.groupEquiv ⟨f₀ x,_⟩) : J) = f₀ x
    rw [e.groupEquiv.symm_apply_apply]
  have hfact (x : Ltilde R u) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (f x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹ := by
    change j (Multiplicative.ofAdd (ρ (e.groupEquiv.symm (f x)) w)) = _
    rw [hfmark]
    exact hconj (inclusion (Ltilde_le_stabilizer u) x) w
  let := finite_stabilizer R u
  let : Finite (Ltilde R u) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer u)) (inclusion_injective _)
  let S := P.mapSurjective (f := f) hf
  have hS : (S : Subgroup (L (K := F))) = (P : Subgroup (Ltilde R u)).map f :=
    Sylow.coe_mapSurjective hf P
  have hfixed (w : s.space.toSubmodule) :
      w ∈ OneCohomology.fixed (σ.comp (S : Subgroup (L (K := F))).subtype) ↔
        j (Multiplicative.ofAdd w) ∈ componentSylowSeed R u P := by
    constructor
    · intro hw
      refine ⟨hjr ▸ ⟨Multiplicative.ofAdd w,rfl⟩,?_⟩
      rintro t ⟨x,hx,rfl⟩
      have hfx : f x ∈ (S : Subgroup (L (K := F))) := hS ▸ mem_map_of_mem f hx
      have hh := hfact x w
      rw [show σ (f x) w = w from hw ⟨f x,hfx⟩] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh.symm
    · intro hw x
      have hx : x.val ∈ (P : Subgroup (Ltilde R u)).map f := by
        rw [←hS]
        exact x.property
      obtain ⟨y,hy,heq⟩ := hx
      change σ x.val w = w
      rw [←heq]
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hfact,hw.2 y.val (mem_map_of_mem _ hy),mul_inv_cancel_right]
  have hnorm : ∀ a ∈ δ.range, ∀ w ∈ OneCohomology.fixed (σ.comp (S : Subgroup (L (K := F))).subtype),
      ρ a w ∈ OneCohomology.fixed (σ.comp (S : Subgroup (L (K := F))).subtype) := by
    rintro _ ⟨a,rfl⟩ w hw
    apply (hfixed _).mpr
    rw [hδ]
    exact (mem_normalizer_iff.mp (hn a.property) _).mp ((hfixed w).mp hw)
  have hδsquare : ∀ a ∈ δ.range, a*a=1 := by
    rintro _ ⟨a,rfl⟩
    rw [←map_mul]
    have ha : a*a=1 := Subtype.ext (hsquare a a.property)
    rw [ha,map_one]
  obtain ⟨ξ,hξ⟩ := exists_twist_fixing_sylow_seed hFl B (hcent ▸ bot_le)
    e.groupEquiv ρ ψ (fun b v => MovedSection.ambientAction_component s e b v)
    p he (fun g w => MovedSection.coverProjection_ambient s e g w)
    hsemi S δ.range hδsquare hnorm
  let η := ξ.comp δ.rangeRestrict
  have hker : η.ker ≤ (centralizer (componentSylowSeed R u P : Set (FreeAmalgam R))).subgroupOf A := by
    intro a ha y hy
    obtain ⟨w,hw⟩ := (show y ∈ j.range from hjr.symm ▸ hy.1)
    have hwfix := (hfixed w.toAdd).mpr (hw ▸ hy)
    have hh := hδ a w.toAdd
    have hfix : ρ (δ a) w.toAdd = w.toAdd :=
      hξ (δ.rangeRestrict a) ha w.toAdd hwfix
    rw [hfix] at hh
    change j w = (a : FreeAmalgam R) * j w * (a : FreeAmalgam R)⁻¹ at hh
    rw [hw] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  let : Finite A := Finite.of_injective (inclusion hA) (inclusion_injective _)
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective
  change ((centralizer (componentSylowSeed R u P : Set (FreeAmalgam R))).subgroupOf A).index ≤ _
  calc
    _ ≤ η.ker.index := Subgroup.index_antitone hker
    _ = Nat.card η.range := Subgroup.index_ker η
    _ ≤ Nat.card (F ≃+* F) := Nat.card_le_card_of_injective _ η.range.subtype_injective

end Model
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full fixed-Sylow seed has elementary-action centralizer index at
most the original field degree. -/
theorem Input.replacement_elementary_seed_index_le_degree
    {u : Vertex d.radical} (hu : color d.radical u = false)
    (P : Sylow 2 (Ltilde d.radical u))
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ stabilizer d.radical u)
    (hn : A ≤ normalizer (componentSylowSeed d.radical u P : Set (FreeAmalgam d.radical)))
    (hsquare : ∀ a ∈ A, a*a=1) :
    (centralizer (componentSylowSeed d.radical u P : Set (FreeAmalgam d.radical))).relIndex A ≤ n := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let B := (K.subgroupOf d.overgroup).map q
  let : B.Normal := (h.replacement_component_image_structure d).2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) B
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d hu
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hbound := elementary_seed_actor_index_le_ringAut hFl s e he j hj hjr κ hκL
    (h.replacement_component_image_structure d).2.2.2.2 hsemi hconj P A hA hn hsquare
  rwa [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two
    (show Nat.card E.Carrier = 2 ^ n by rw [E.card_eq,hE])] at hbound

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
