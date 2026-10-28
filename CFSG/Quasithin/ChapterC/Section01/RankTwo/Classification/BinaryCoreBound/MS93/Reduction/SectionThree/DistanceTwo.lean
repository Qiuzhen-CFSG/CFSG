module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.Frattini
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.Sections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.LocalModules
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.NaturalCore
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.DistanceTwo.SmallExtension
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# The binary distance-two core dichotomy

For the actual commutator core [Q_alpha,Ltilde_alpha], critical distance two
forces either core = U_alpha or trivial Frattini subgroup of core.

Burnside's basis-kernel theorem handles core contained in Phi(Q_alpha)X_alpha,
using the proved binary identity [X_alpha,Ltilde_alpha] = U_alpha. Otherwise
the local module calculation excludes the doubled and nonsplit alternatives
and constructs the actual natural U. The critical-pair estimates supply a
natural quotient core/U, an element outside U with centralizer index at most
two, and generation of core by involutions.

Transitivity of the natural action on the seven nonidentity elements of U
makes every characteristic subgroup of core contained in U trivial or all
of U. The central-extension bound therefore makes core commutative, and its
involution generation gives trivial Frattini. All characteristic subgroups
and centralizers in this step are inside core. Only finite vertex subgroups
are used; the ambient free amalgam remains infinite.

This proves the binary dichotomy from the first assertion of
Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two* (1993),
(3.6), printed pp.870--872. The additional source conclusion identifying
the two module markings is not needed for this dichotomy. The parent
SectionThree module can convert the dichotomy to core abelianness.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] {L R : Subgroup M}

private theorem characteristic_core_subgroup (source : LocalSource L R)
    (natural : NaturalU R source.projection)
    (D : Subgroup (core R (alpha R))) (hchar : D.Characteristic)
    (hD : D ≤ (U R (alpha R)).subgroupOf (core R (alpha R))) :
    D = ⊥ ∨ D = (U R (alpha R)).subgroupOf (core R (alpha R)) := by
  rcases D.bot_or_exists_ne_one with hz | ⟨x, hx, hxne⟩
  · exact Or.inl hz
  right
  apply le_antisymm hD
  intro y hy
  by_cases hyne : y = 1
  · simpa only [hyne] using D.one_mem
  let xU : U R (alpha R) := ⟨x, hD hx⟩
  let yU : U R (alpha R) := ⟨y, hy⟩
  have hxcoord : (natural.equiv xU).toAdd ≠ 0 := by
    intro h
    have hh : natural.equiv xU = natural.equiv 1 := by
      simpa using congrArg Multiplicative.ofAdd h
    exact hxne (Subtype.ext (congrArg (fun z : U R (alpha R) => (z : FreeAmalgam R))
      (natural.equiv.injective hh)))
  have hycoord : (natural.equiv yU).toAdd ≠ 0 := by
    intro h
    have hh : natural.equiv yU = natural.equiv 1 := by
      simpa using congrArg Multiplicative.ofAdd h
    exact hyne (Subtype.ext (congrArg (fun z : U R (alpha R) => (z : FreeAmalgam R))
      (natural.equiv.injective hh)))
  obtain ⟨g, hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ hxcoord hycoord
  obtain ⟨m, hm⟩ := source.projection_surjective (natural.marking.symm g)
  have hmM : embedM R m ∈ Mbar R := ⟨m, rfl⟩
  have hmC : embedM R m ∈ normalizer (core R (alpha R) : Set (FreeAmalgam R)) := by
    apply DistanceTwo.core_normalized (alpha R)
    simpa only [alpha, stabilizer_m_base] using hmM
  let c := (core R (alpha R)).normalizerMonoidHom ⟨embedM R m, hmC⟩ x
  have hcD : c ∈ D := characteristic_iff_le_comap.mp hchar _ hx
  let cU : U R (alpha R) := ⟨c, hD hcD⟩
  have hc : cU = yU := by
    apply natural.equiv.injective
    have h := natural.action m xU cU rfl
    rw [hm, natural.marking.apply_symm_apply, hg] at h
    exact congrArg Multiplicative.ofAdd h
  have hcy : c = y := Subtype.ext (congrArg (fun z : U R (alpha R) => (z : FreeAmalgam R)) hc)
  exact hcy ▸ hcD

/-- The actual natural quotient and small centralizer force commutativity;
involution generation then gives trivial Frattini. The quotient marking
need not agree with the marking on U for this conclusion. -/
theorem DistanceTwo.frattini_eq_bot_of_extensionEstimates [Finite M]
    (source : LocalSource L R) (geometry : Geometry R) (hb : 0 < geometry.b R)
    (natural : NaturalU R source.projection) (estimates : DistanceTwo.ExtensionEstimates source) :
    frattini (core R (alpha R)) = ⊥ := by
  let K := core R (alpha R)
  let N := (U R (alpha R)).subgroupOf K
  let : Finite K := DistanceTwo.finite_core (alpha R)
  let : N.Normal := DistanceTwo.U_subgroupOf_core_normal (alpha R) rfl
  have hN : Nat.card N = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe
      (DistanceTwo.U_le_core geometry hb (alpha R) rfl)).toEquiv).trans natural.card
  let q := estimates.quotient
  let e : (K ⧸ N) ≃* Multiplicative (Fin 3 → ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq q.kernel.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q.projection q.surjective)
  let : IsElementaryAbelian 2 (Multiplicative (Fin 3 → ZMod 2)) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      change (2 : ℕ) • x.toAdd = 0
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
      exact zero_smul (ZMod 2) x.toAdd) }
  let : IsElementaryAbelian 2 (K ⧸ N) :=
    IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hquot : Nat.card (K ⧸ N) = 8 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (Fin 3 → ZMod 2) = 8
    simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  let : IsMulCommutative K :=
    DistanceTwo.SmallExtension.isMulCommutative_of_small_centralizer N
      (DistanceTwo.U_subgroupOf_core_le_center (alpha R) rfl) hN hquot
      (characteristic_core_subgroup source natural) estimates.small_centralizer
  exact DistanceTwo.frattini_eq_bot_of_commutative_of_involution_generation
    estimates.involution_generation

/-- The binary core dichotomy from MS93 (3.6), with every local module and
extension premise discharged from the source hypotheses at distance two.
Here core is [Q_alpha,Ltilde_alpha], not the radius-two group V_alpha. -/
theorem LocalSource.core_eq_U_or_frattini_eq_bot_of_b_two [Finite M]
    (source : LocalSource L R) (geometry : Geometry R) (hb : geometry.b R = 2) :
    core R (alpha R) = U R (alpha R) ∨ frattini (core R (alpha R)) = ⊥ := by
  by_cases hsmall : core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)
  · exact Or.inl (source.core_eq_U_of_le_frattini_sup (alpha R) rfl
      (DistanceTwo.X_commutator_eq_U source geometry hb) hsmall)
  · obtain ⟨natural⟩ := DistanceTwo.naturalU_of_not_le_frattini_sup source geometry hb hsmall
    obtain ⟨estimates⟩ := DistanceTwo.NaturalCore.extensionEstimates source geometry hb natural hsmall
    exact Or.inr (DistanceTwo.frattini_eq_bot_of_extensionEstimates source geometry
      (by omega) natural estimates)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
