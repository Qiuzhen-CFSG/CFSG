module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.StarComparison
public import Theory.Representation.SymplecticNaturalNormalizer.RootFixedCover
/-!
# A critical root detects movement of the endpoint intersection

An actor fixing Z_endpoint intersect Q_start fixes all lifts of the natural
critical root hyperplane. Its image therefore belongs to that same full root
group. Subtracting the matching original Z_start element leaves the literal
kernel C(Z_endpoint), so its displacement lies in the critical commutator.

This supplies the noncentralization step in the symplectic branch of
Meierfrankenfeld--Stellmacher (1993), (3.4), printed p.868. The full original
source application is in SeedMovementSource.
-/

public section
noncomputable section
open Subgroup Representation Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open ChapterB.QuasisimpleSource Representation.SymplecticFourOrthogonalCover SourceComparison
variable {H J V F : Type*} [Group H] [Finite H] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  {ρ : Representation (ZMod 2) J V} {B : Subgroup J} [B.Normal]
  {R : Subgroup H} {geometry : Geometry R} {a z : Vertex R}

omit [Finite H] in
theorem critical_seed_displacement_le_of_fixed_intersection
    (path : CriticalPath R geometry a z) (hb : 0 < geometry.b R)
    (hCa : C R a = Q R a) (hF : 2 < Nat.card F)
    (s : MovedSection ρ B)
    (e : ActionEquiv (s.action.comp B.subtype) (binaryNatural (K := F)))
    (hp : IsCover (MovedSection.coverProjection s e))
    (hcent : centralizer (B : Set J) = ⊥)
    (j : Multiplicative s.space.toSubmodule →* FreeAmalgam R) (hj : Function.Injective j)
    (hjr : j.range = U R z)
    (κ : stabilizer R z →* J)
    (hκC : κ.ker.map (stabilizer R z).subtype = C R z)
    (hκ : ∀ x : stabilizer R z, ∀ w : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (κ x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹)
    (β : Z R a →* L (K := F))
    (hAZ : Z R a ≤ stabilizer R z)
    (hβmark : ∀ x : Z R a, (e.groupEquiv.symm (β x) : J)=κ (inclusion hAZ x))
    (hβ : ∀ x : Z R a, ∀ w : s.space.toSubmodule,
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) w)) =
        (x : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (x : FreeAmalgam R)⁻¹)
    (hd : Module.finrank F (displacementSpace (β.range.map (commutator (Sp F)).subtype))=1)
    (hc : Nat.card β.range=Nat.card F)
    (Y : Subgroup (FreeAmalgam R)) (hYZ : Y ≤ stabilizer R z)
    (hfix : Y ≤ centralizer ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _)) :
    ⁅Z R z,Y⁆ ≤ ⁅Z R a,Z R z⁆ := by
  let p := MovedSection.coverProjection s e
  let σ := MovedSection.coverAction s e
  let ψ := MovedSection.ambientAction s e
  let d : L (K := F) ≃* Sp F :=
    (MulEquiv.subgroupCongr
      (OneCohomology.SymplecticFour.LargeField.commutator_eq_top hF)).trans Subgroup.topEquiv
  let : IsElementaryAbelian 2 (Z R a) := geometry.Z_elementary hb a path.start_color
  have hP : IsPGroup 2 β.range :=
    (IsElementaryAbelian.isPGroup 2 (Z R a)).of_surjective β.rangeRestrict β.rangeRestrict_surjective
  have hZA : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  have hroot (y : Y) : ∃ x : Z R a,
      κ (inclusion hAZ x) = κ (inclusion hYZ y) := by
    have hfixed (w : s.space.toSubmodule)
        (hw : w ∈ OneCohomology.fixed (σ.comp β.range.subtype)) :
        s.space.toRepresentation (κ (inclusion hYZ y)) w = w := by
      have hjw : j (Multiplicative.ofAdd w) ∈ U R z := by
        rw [←hjr]
        exact ⟨Multiplicative.ofAdd w,rfl⟩
      have hcentral : j (Multiplicative.ofAdd w) ∈ centralizer (Z R a : Set _) := by
        intro x hx
        have he := hw (⟨β ⟨x,hx⟩,⟨⟨x,hx⟩,rfl⟩⟩ : β.range)
        change MovedSection.coverAction s e (β ⟨x,hx⟩) w = w at he
        have hh := hβ ⟨x,hx⟩ w
        rw [he] at hh
        exact mul_inv_eq_iff_eq_mul.mp hh.symm
      have hQa : j (Multiplicative.ofAdd w) ∈ Q R a := by
        rw [←hCa]
        exact ⟨hZA (U_le_Z z hjw),hcentral⟩
      apply Multiplicative.ofAdd.injective
      apply hj
      rw [hκ]
      have hh := hfix y.property _ ⟨U_le_Z z hjw,hQa⟩
      change (y : FreeAmalgam R) * j (Multiplicative.ofAdd w) * (y : FreeAmalgam R)⁻¹ = _
      rw [←hh,mul_inv_cancel_right]
    obtain ⟨t,ht,he⟩ := SymplecticNaturalNormalizer.mem_root_image_of_fixes_cover_seed B
      (hcent ▸ bot_le) hF (e.groupEquiv.trans d) ψ
      (fun b v => MovedSection.ambientAction_component s e b v)
      p hp β.range hP hd hc (κ (inclusion hYZ y))
      (s.space.toRepresentation (κ (inclusion hYZ y)))
      (fun w => MovedSection.coverProjection_ambient s e _ w) hfixed
    obtain ⟨x,rfl⟩ := ht
    refine ⟨x,?_⟩
    rw [←hβmark x]
    exact he
  apply commutator_le.mpr
  intro u hu y hy
  obtain ⟨x,hx⟩ := hroot ⟨y,hy⟩
  let c : stabilizer R z := (inclusion hAZ x)⁻¹ * inclusion hYZ ⟨y,hy⟩
  have hc : c ∈ κ.ker := by
    change κ c=1
    simp only [c,map_mul,map_inv,hx,inv_mul_cancel]
  have hcC : (c : FreeAmalgam R) ∈ C R z := by
    rw [←hκC]
    exact ⟨c,hc,rfl⟩
  have huc : Commute u (c : FreeAmalgam R) := hcC.2 u hu
  have hyc : y = (x : FreeAmalgam R) * (c : FreeAmalgam R) := by
    change y = (x : FreeAmalgam R) * ((x : FreeAmalgam R)⁻¹ * y)
    simp
  rw [hyc,commutatorElement_mul_right_eq_mul_conj,huc.commutator_eq]
  simpa only [mul_one,mul_inv_cancel_right] using
    (show ⁅u,(x : FreeAmalgam R)⁆ ∈ ⁅Z R a,Z R z⁆ from by
      rw [commutator_comm]
      exact commutator_mem_commutator hu x.property)
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
