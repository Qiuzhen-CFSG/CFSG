module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorGeometry
public import Theory.Representation.NormalConstituentDisplacement
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Displacement on the original full module in the remaining tensor branch

The seed is a simple constituent for the normal component orbit. An ambient
operator moving fewer dimensions than this constituent preserves it. The
checked tensor-normalizer bound then makes every operator moving fewer than n
full-module dimensions centralize the seed. Apply this to each M-conjugate
of that operator: it centralizes every M-conjugate of the seed, hence the
whole original full module.

Thus every nonidentity action of the actual full automizer moves at least n
binary dimensions, and its minimum-involution parameter is at least n.
This does not assume that the seed is M-invariant or equals the full module.
It supplies the displacement premise of E.6.3 on the actual ambient carrier,
needed for the n > 2 branch of source 9.2.3.
Source: Aschbacher--Smith 3.2.1, 9.1.2(1), 9.2.3, printed pp.579,729--730,
and 10.1.1--2,10.2.3, pp.741--742,745, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
open Representation.BinaryOffender.NaturalTensor
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private theorem seed_le_full : D.seed ≤ D.fullModule :=
  (le_componentOrbit D.seed T).trans (le_componentOrbit _ _)

private def seedInFull : Additive D.seed →ₗ[ZMod 2] Additive D.fullModule :=
  (inclusion (seed_le_full D)).toAdditive.toZModLinearMap 2

private theorem seedInFull_injective : Function.Injective (seedInFull D) := by
  intro v w he
  exact Additive.toMul.injective ((inclusion_injective (seed_le_full D)) he)

private def seedInFullIntertwiner :
    Representation.IntertwiningMap ((originalSeedAction D).comp
      (subgroupOfEquivOfLe (localOrbit T L).le_normalizer).toMonoidHom)
      ((originalFullAction D).comp ((localOrbit T L).subgroupOf D.maximalLocal).subtype) where
  toLinearMap := seedInFull D
  isIntertwining' _ := by ext v; rfl

private theorem seedInFull_range_irreducible {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) : (seedInFullIntertwiner D).range.toRepresentation.IsIrreducible := by
  let e := subgroupOfEquivOfLe (localOrbit T L).le_normalizer
  let τ : Representation (ZMod 2) ((localOrbit T L).subgroupOf D.maximalLocal)
      (Additive D.seed) := (originalSeedAction D).comp e.toMonoidHom
  let : τ.IsIrreducible := (irreducible_comp_surjective_iff e.toMonoidHom e.surjective
    (originalSeedAction D)).mpr (originalSeedAction_irreducible D c)
  let f := seedInFullIntertwiner D
  let a : τ.Equiv f.range.toRepresentation := Representation.Equiv.mk
    (LinearEquiv.ofInjective f.toLinearMap (seedInFull_injective D)) (fun _ => by ext v; rfl)
  exact (RepEquiv.ofRepresentationEquiv a.symm).irreducible_of_euqiv inferInstance

/-- Small displacement on the full module forces preservation of the original seed. -/
theorem original_seed_stable_of_full_displacement_lt
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (m : D.maximalLocal)
    (hsmall : operatorFixedCodim (originalFullAction D m) <
      Module.finrank (ZMod 2) (Additive D.seed)) :
    (m : G) ∈ normalizer (D.seed : Set G) := by
  let N := (localOrbit T L).subgroupOf D.maximalLocal
  let : N.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : FiniteDimensional (ZMod 2) (Additive D.fullModule) := Module.Finite.of_finite
  have hr : Module.finrank (ZMod 2) (seedInFullIntertwiner D).range.toSubmodule =
      Module.finrank (ZMod 2) (Additive D.seed) :=
    (LinearEquiv.ofInjective (seedInFull D) (seedInFull_injective D)).finrank_eq.symm
  have hs := map_constituent_eq_self_of_displacement_lt (originalFullAction D) N m
    (seedInFullIntertwiner D).range (seedInFull_range_irreducible D c)
    (by simpa only [operatorFixedCodim, Module.End.one_eq_id, hr] using hsmall)
  apply mem_normalizer_iff.mpr
  intro v
  constructor
  · intro hv
    have hh : seedInFull D (Additive.ofMul ⟨v,hv⟩) ∈
        (seedInFullIntertwiner D).range.toSubmodule := ⟨_,rfl⟩
    have hm : originalFullAction D m (seedInFull D (Additive.ofMul ⟨v,hv⟩)) ∈
        (seedInFullIntertwiner D).range.toSubmodule := hs ▸ Submodule.mem_map_of_mem hh
    obtain ⟨w,hw⟩ := hm
    have he := congrArg (fun a : Additive D.fullModule => (a.toMul : G)) hw
    change (w.toMul : G) = (m:G)*v*(m:G)⁻¹ at he
    exact he ▸ w.toMul.property
  · intro hv
    have hV : v ∈ D.fullModule := (mem_normalizer_iff.mp
      (D.maximalLocal_normalizes_fullModule m.property) v).mpr ((seed_le_full D) hv)
    have hh : seedInFull D (Additive.ofMul ⟨(m:G)*v*(m:G)⁻¹,hv⟩) ∈
        (seedInFullIntertwiner D).range.toSubmodule := ⟨_,rfl⟩
    rw [←hs] at hh
    obtain ⟨w,hw,he⟩ := hh
    obtain ⟨z,hz⟩ := hw
    have he' : w = Additive.ofMul ⟨v,hV⟩ := (apply_bijective (originalFullAction D) m).injective he
    have hz' := congrArg (fun a : Additive D.fullModule => (a.toMul : G)) (hz.trans he')
    change (z.toMul : G) = v at hz'
    exact hz' ▸ z.toMul.property

/-- Restriction to the unchanged seed does not increase displacement. -/
theorem original_seed_displacement_le_full (m : D.maximalLocal)
    (hs : (m:G) ∈ normalizer (D.seed : Set G)) :
    operatorFixedCodim (originalSeedNormalizerAction D ⟨m,hs⟩) ≤
      operatorFixedCodim (originalFullAction D m) := by
  let : FiniteDimensional (ZMod 2) (Additive D.fullModule) := Module.Finite.of_finite
  exact operatorFixedCodim_le_of_injective _ _ (seedInFull D)
    (seedInFull_injective D) (fun _ => rfl)

/-- Every action moving fewer than n dimensions fixes the original seed pointwise. -/
theorem original_even_seed_fixed_of_full_displacement_lt
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (m : D.maximalLocal) (hsmall : operatorFixedCodim (originalFullAction D m) < n) :
    (m:G) ∈ centralizer (D.seed : Set G) := by
  have hd := original_nonseparated_even_seed_finrank_eq D c n hn e ht htn hsep
  have hs := original_seed_stable_of_full_displacement_lt D c m (by omega)
  have he : originalSeedNormalizerAction D ⟨m,hs⟩ = 1 := by
    by_contra hmove
    have hh := original_even_seed_ambient_displacement_ge D c n hn e ht htn hsep
      m m.property hs hmove
    have hb := original_seed_displacement_le_full D m hs
    omega
  intro v hv
  have hh := congrArg (fun w : Additive D.seed => (w.toMul : G))
    (LinearMap.congr_fun he (Additive.ofMul ⟨v,hv⟩))
  change (m:G)*v*(m:G)⁻¹ = v at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The bound holds for every element of M on the whole full module. -/
theorem original_even_full_displacement_ge
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (m : D.maximalLocal) (hmove : originalFullAction D m ≠ 1) :
    n ≤ operatorFixedCodim (originalFullAction D m) := by
  let : FiniteDimensional (ZMod 2) (Additive D.fullModule) := Module.Finite.of_finite
  by_contra! hsmall
  have hfix (k : D.maximalLocal) :
      ((k⁻¹*m*k : D.maximalLocal) : G) ∈ centralizer (D.seed : Set G) := by
    apply original_even_seed_fixed_of_full_displacement_lt D c n hn e ht htn hsep
    have he : operatorFixedCodim (originalFullAction D (k⁻¹*m*k)) =
        operatorFixedCodim (originalFullAction D m) := by
      change Module.finrank (ZMod 2) (originalFullAction D (k⁻¹*m*k) - LinearMap.id).range =
        Module.finrank (ZMod 2) (originalFullAction D m - LinearMap.id).range
      rw [←fixedCodim_zpowers_eq_displacement_rank,←fixedCodim_zpowers_eq_displacement_rank]
      simpa only [inv_inv] using fixedCodim_zpowers_conj (originalFullAction D) m k⁻¹
    rwa [he]
  have hc : D.fullModule ≤ centralizer ({(m:G)} : Set G) := by
    rw [D.fullModule_eq_seed_orbit]
    apply iSup_le
    intro k
    rintro _ ⟨v,hv,rfl⟩ a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    have hh := hfix k v hv
    change v*((k:G)⁻¹*(m:G)*(k:G)) = ((k:G)⁻¹*(m:G)*(k:G))*v at hh
    change (m:G)*((k:G)*v*(k:G)⁻¹) = ((k:G)*v*(k:G)⁻¹)*(m:G)
    calc
      _ = (k:G)*(((k:G)⁻¹*(m:G)*(k:G))*v)*(k:G)⁻¹ := by group
      _ = (k:G)*(v*((k:G)⁻¹*(m:G)*(k:G)))*(k:G)⁻¹ := by rw [hh]
      _ = _ := by group
  apply hmove
  apply LinearMap.ext
  intro v
  apply Additive.toMul.injective
  apply Subtype.ext
  change (m:G)*(v.toMul:G)*(m:G)⁻¹ = (v.toMul:G)
  rw [hc v.toMul.property m rfl,mul_inv_cancel_right]

/-- Every nonidentity element of the actual full automizer has displacement at least n. -/
theorem original_even_automizer_displacement_ge
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (a : ChapterE.Automizer D.fullModule) (ha : a ≠ 1) :
    n ≤ operatorFixedCodim (ChapterE.automizerRepresentation D.fullModule a) := by
  obtain ⟨m,hm⟩ := D.fullModule.normalizerMonoidHom.rangeRestrict_surjective a
  let m' : D.maximalLocal := ⟨m,(source_fullModule_normalizer D).le m.property⟩
  have he : originalFullAction D m' = ChapterE.automizerRepresentation D.fullModule a := by
    rw [←hm]
    rfl
  have hmove : originalFullAction D m' ≠ 1 := by
    rw [he]
    intro hz
    apply ha
    apply ChapterE.automizerRepresentation_injective D.fullModule
    simpa only [map_one] using hz
  exact he ▸ original_even_full_displacement_ge D c n hn e ht htn hsep m' hmove

/-- The actual ambient minimum-involution parameter is at least n. -/
theorem original_even_full_localM_ge
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    n ≤ ChapterE.localM D.fullModule := by
  let : FiniteDimensional (ZMod 2) (Additive D.fullModule) := Module.Finite.of_finite
  apply le_csInf ⟨_,Set.mem_insert _ _⟩
  rintro k (rfl | ⟨a,ha,rfl⟩)
  · have hd := original_nonseparated_even_seed_finrank_eq D c n hn e ht htn hsep
    have hb := LinearMap.finrank_le_finrank_of_injective (seedInFull_injective D)
    omega
  · exact (original_even_automizer_displacement_ge D c n hn e ht htn hsep a
      (by intro he; simp [he] at ha)).trans
      (operatorFixedCodim_le_fixedCodim (ChapterE.automizerRepresentation D.fullModule)
        (zpowers a) (mem_zpowers a))

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
