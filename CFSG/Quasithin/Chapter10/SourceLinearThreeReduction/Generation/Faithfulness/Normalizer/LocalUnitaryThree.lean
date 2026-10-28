module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalBounds
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalFiniteExclusions
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.LocalBinaryExclusions
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.BinaryClosure
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.StandardAction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport

/-!
# The binary unitary-three normalizer component

A nonidentity two-subgroup of PSU₃(2ᶠ) has a unique fixed isotropic point:
its containing Sylow subgroup acts regularly away from that point. Its
normalizer therefore lies in the solvable Borel. The actual perfect residual
cannot normalize the nontrivial image of the original local module there.
Covering uniqueness and the proved outer action discharge residual placement.

The private geometric transport reuses the proof in Chapter C,
OrdinaryPlacement/BinaryUnitaryExclusion, without changing that shared module.
Source: Aschbacher--Smith F.1.3(1), 4.4.10--12 and 10.2.3(2),
printed pp.259--260,621--623,745.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter10.LocalFixed.HallUnitaryThree
private theorem normalizer_le_of_regular
    {G Ω : Type*} [Group G] [MulAction G Ω]
    (S : Subgroup G) (α : Ω)
    (hN : normalizer (S : Set G) = MulAction.stabilizer G α)
    (hreg : ∀ a b : Ω, a ≠ α → b ≠ α → ∃! s : S, (s : G) • a = b)
    (P : Subgroup G) (hne : P ≠ ⊥) (hPS : P ≤ S) :
    normalizer (P : Set G) ≤ normalizer (S : Set G) := by
  intro g hg
  rw [hN, MulAction.mem_stabilizer_iff]
  by_contra hmove
  obtain ⟨r,hr⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hc : g⁻¹ * (r : G) * g ∈ P := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer (P : Set G)).inv_mem hg) (r : G)).mp r.property
  have hfix : (g⁻¹ * (r : G) * g) • α = α :=
    MulAction.mem_stabilizer_iff.mp (hN ▸ S.le_normalizer (hPS hc))
  have hfix' : (r : G) • (g • α) = g • α := by
    have hh := congrArg (fun a => g • a) hfix
    simpa only [mul_smul,smul_inv_smul] using hh
  obtain ⟨s,_,hs⟩ := hreg (g • α) (g • α) hmove hmove
  have he : (⟨r,hPS r.property⟩ : S) = 1 :=
    (hs _ hfix').trans (hs 1 (one_smul _ _)).symm
  exact hr (Subtype.ext (congrArg (fun s : S => (s : G)) he))

private theorem standard_two_normalizer_solvable
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    {f : ℕ} (hf : 0 < f)
    (hc : Nat.card F = (2 ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ f))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥) :
    Group.IsSolvable (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  obtain ⟨ρ,α,S,_,_,hsol,_,_,_,hN,hreg,_⟩ :=
    ChapterF.Source.Unitary.standard_psu_borel_data J f hf hc hconj hJ
  let U := ProjectiveSpecialUnitaryMatrixGroup J
  let Ω := {l : Projectivization F (Fin 3 → F) // l ∈
    {l | ∃ (v : Fin 3 → F) (hv : v ≠ 0), l = Projectivization.mk F v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}}
  let ρ' : U →* Equiv.Perm Ω := ρ
  let : MulAction U Ω := MulAction.compHom Ω ρ'
  obtain ⟨T,hPT⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq U T S
  let e := MulAut.conj g
  have hm : (T : Subgroup U).map e.toMonoidHom = (S : Subgroup U) :=
    congrArg Sylow.toSubgroup hg
  have hN' : normalizer (S : Set U) = MulAction.stabilizer U (α : Ω) := hN
  have hreg' : ∀ a b : Ω, a ≠ α → b ≠ α → ∃! s : S, (s : U) • a = b := hreg
  have hn : normalizer (P.map e.toMonoidHom : Set U) ≤ normalizer (S : Set U) :=
    normalizer_le_of_regular (G := U) (Ω := Ω) (S : Subgroup U) α hN' hreg'
      (P.map e.toMonoidHom)
      (fun h => hne ((map_eq_bot_iff_of_injective P e.injective).mp h))
      ((map_mono hPT).trans_eq hm)
  have hn' : (normalizer (P : Set U)).map e.toMonoidHom ≤ normalizer (S : Set U) := by
    rwa [map_equiv_normalizer_eq]
  let j := (normalizer (P : Set U)).equivMapOfInjective e.toMonoidHom e.injective
  let : Group.IsSolvable (normalizer (S : Set U)) := hsol
  exact Group.isSolvable_of_isSolvable_injective
    (f := (inclusion hn').comp j.toMonoidHom) ((inclusion_injective hn').comp j.injective)

private theorem model_two_normalizer_solvable
    {U : Type*} [Group U] [Finite U] {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSU U 3 (2 ^ f))
    (P : Subgroup U) (hp : IsPGroup 2 P) (hne : P ≠ ⊥) :
    Group.IsSolvable (normalizer (P : Set U)) := by
  obtain ⟨F,_,_,J,hc,hconj,⟨e⟩⟩ := hm
  obtain ⟨C,hC⟩ := ChapterF.Source.Unitary.FormTransport.exists_standard_basis J f hf hc hconj
  let J₀ := ChapterF.Source.Unitary.FormTransport.standardForm J
  let a := e.trans (ChapterF.Source.Unitary.FormTransport.projectiveEquiv J C hC)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) := Finite.of_surjective a a.surjective
  have hn := standard_two_normalizer_solvable J₀ hf hc hconj rfl
    (P.map a.toMonoidHom) (hp.map _) (fun he => hne
      ((map_eq_bot_iff_of_injective P a.injective).mp he))
  let : Group.IsSolvable ((normalizer (P : Set U)).map a.toMonoidHom) := by
    rwa [map_equiv_normalizer_eq]
  let j := (normalizer (P : Set U)).equivMapOfInjective a.toMonoidHom a.injective
  exact Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective

end CFSG.Quasithin.Chapter10.LocalFixed.HallUnitaryThree
namespace CFSG.Quasithin.Chapter10.LocalFixed
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (V : Subgroup G) (hVV : V ≤ D.fullModule) (hne : V ≠ ⊥)
    (hVX : V = ⁅V,localOrbit T L⁆)
    (hNV : localJoin T L ≤ normalizer (V : Set G))
  (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (V : Set G))
  (K : Subgroup (normalizer (B : Set G)))
  (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K)
include D hn hVV hne hVX hNV hBC hodd hBV hFK

/-- The solvable Borel cannot contain the original perfect residual moving
a nontrivial elementary layer in the literal central quotient. -/
theorem source_nonnormal_oddNormalizer_no_placed_binary_unitary_three_component
    {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 3 (2 ^ f)) : False := by
  apply source_nonnormal_oddNormalizer_no_component_of_local_rank_bound
    D hn V hVV hne hVX hNV B hBC hodd hBV K hFK (MulEquiv.refl (K ⧸ center K))
  intro A Q hA hQ hne hN p hp ho
  let : Group.IsSolvable (normalizer (Q : Set (K ⧸ center K))) :=
    HallUnitaryThree.model_two_normalizer_solvable hf hm Q hQ hne
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hN)
  let := hA
  have hs : Subsingleton A := by
    by_contra! hs
    exact Group.IsPerfect.not_isSolvable A inferInstance
  let := hs
  let : Fact p.Prime := ⟨hp⟩
  have he : primeRank p A = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr (by
    rw [Nat.card_unique]
    exact hp.not_dvd_one)
  omega


end CFSG.Quasithin.Chapter10.LocalFixed
