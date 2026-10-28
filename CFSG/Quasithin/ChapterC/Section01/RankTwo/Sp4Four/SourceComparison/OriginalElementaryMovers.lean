module
public import Theory.Representation.SymplecticNaturalNormalizer.LargeElementary
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalAbelianMoverGeneration

/-!
# Elementary cross images retain the original symplectic component

The literal image of an original stabilizer actor has kernel its intersection
with Q_a. If every square lies in Q_a, the image is elementary abelian.
An image with more than sixteen elements cannot contain an outer natural
involution, so it lies in the same marked residual image. Pulling back through
the entire kernel gives E <= Ltilde_a Q_a and [E,E] <= Q_a.

GenerationTwoSymplecticElementarySelection applies this to the actual
neighboring mover of relative order at least sixty-four, then uses the checked
point-radical generator and overlapping-path construction.
Source: MS93 (5.5), pp.915--917, in the original field-four geometry of
Aschbacher--Smith 9.3.10, pp.734--735.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H J : Type*} [Group H] [Finite H] [Group J] [Finite J]

/-- An original actor with elementary cross image of order greater than
sixteen is inner and abelian modulo the full original kernel. -/
theorem original_large_elementary_mover_placement
    (R : Subgroup H) (hms : MSCharacteristicCondition R)
    (hp : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 H ≤ R)
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hfaith : centralizer (omegaOrbit R : Set H) = pCore 2 H)
    (q : H →* J) (hq : Function.Surjective q) (hcore : q.ker = pCore 2 H)
    [((pResidual 2 H).map q).Normal]
    [IsSimpleGroup ((pResidual 2 H).map q)] [IsQuasisimple ((pResidual 2 H).map q)]
    (hc : Nat.card ((pResidual 2 H).map q) = 979200)
    (hC : centralizer ((pResidual 2 H).map q : Set J) = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple ((pResidual 2 H).map q))
    {a : Vertex R} (ha : color R a = false)
    (E : Subgroup (FreeAmalgam R)) (hES : E ≤ stabilizer R a)
    (hlarge : 16 < (Q R a).relIndex E)
    (hsquare : ∀ x ∈ E, x^2 ∈ Q R a) :
    E ≤ Ltilde R a ⊔ Q R a ∧ ⁅E,E⁆ ≤ Q R a := by
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 H)) := omegaCenterIn_elementary _
  let hk := hcore.trans (centralOmega_centralizer R hQR hself hfaith).symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q hq hk) ((pResidual 2 H).map q)
  obtain ⟨F,hF,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hconj,hproj,hker⟩ :=
    ambient_initial_cover_at_vertex R hms hp hne hQR hself hfaith q hq hcore hc hC hsq ha
  have hFc : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  let S := stabilizer R a
  let E₀ := E.subgroupOf S
  let E₁ := E₀.map κ
  have hκker : κ.ker = (Q R a).subgroupOf S := by
    apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
    rw [hκQ,map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1)]
  have hs (x : E₁) : x^2=1 := by
    obtain ⟨y,hy,hyx⟩ := x.property
    apply Subtype.ext
    change x.val^2=1
    rw [←hyx,←map_pow]
    change y^2 ∈ κ.ker
    rw [hκker]
    exact hsquare y.val hy
  let : IsMulCommutative E₁ := ⟨⟨fun x y =>
    Commute.of_orderOf_dvd_two (fun z => orderOf_dvd_of_pow_eq_one (hs z)) x y⟩⟩
  let : IsElementaryAbelian 2 E₁ := {
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hs }
  have hE₁index : Nat.card E₁ = (Q R a).relIndex E := by
    rw [←relIndex_ker,hκker]
    have hh := relIndex_map_map_of_injective ((Q R a).subgroupOf S) E₀ S.subtype_injective
    rw [map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1),
      map_subgroupOf_eq_of_le hES] at hh
    exact hh.symm
  let d : L (K := F.Carrier) ≃* Sp F.Carrier :=
    (MulEquiv.subgroupCongr
      (Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top
        (by omega : 2 < Nat.card F.Carrier))).trans Subgroup.topEquiv
  have hE₁B : E₁ ≤ (pResidual 2 H).map q :=
    SymplecticNaturalNormalizer.large_elementary_le_component hFc _ (e.groupEquiv.trans d)
      (MovedSection.ambientAction s e) hψ
      (fun b v => MovedSection.ambientAction_component s e b v) E₁
      (hE₁index.symm ▸ hlarge)
  have hE₀ := map_le_map_iff.mp (show E₀.map κ ≤ ((Ltilde R a).subgroupOf S).map κ by
    rw [hκL]; exact hE₁B)
  have hEin := map_mono (f := S.subtype) hE₀
  rw [map_subgroupOf_eq_of_le hES,Subgroup.map_sup,
    map_subgroupOf_eq_of_le (Ltilde_le_stabilizer a),hκQ] at hEin
  refine ⟨hEin,?_⟩
  have hcomm : ⁅E₀,E₀⁆ ≤ κ.ker := by
    change ⁅E₀,E₀⁆ ≤ (⊥ : Subgroup J).comap κ
    apply (map_le_iff_le_comap).mp
    rw [map_commutator]
    change ⁅E₁,E₁⁆ ≤ ⊥
    exact (commutator_self_eq_bot_iff.mpr inferInstance).le
  have hm := map_mono (f := S.subtype) hcomm
  rwa [map_commutator,map_subgroupOf_eq_of_le hES,hκQ] at hm
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
