module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SeedIndex

/-!
# The first symplectic star comparison at arbitrary degree

A bad star selects an escaping full-Sylow seed. Its common edge places the
full endpoint intersection in the seed normalizer. The intersection has
exponent two, so its action on the seed has index at most n, while the
critical root comparison gives index at least 2ⁿ. This contradiction proves
[Z-star-alpha,L-alpha] <= Z-alpha on the actual characteristic replacement.

The argument retains all central attachments and uses the original field
degree. It closes both penultimate branches together by measuring action on
the selected seed itself. Source: MS93 (3.4), printed pp.868--869.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- An escaping seed from a bad source star contradicts the exact lower and
upper action indices on the full endpoint intersection. -/
theorem Input.replacement_no_escaping_star_seed
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    {z : Vertex d.radical} (path : CriticalPath d.radical geometry (alpha d.radical) z)
    (Y : Subgroup d.radical) (P₀ : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P₀)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical)))
    {u t : Vertex d.radical} (hu : color d.radical u = false)
    (hat : Adjacent d.radical (alpha d.radical) t) (hut : Adjacent d.radical u t)
    (P : Sylow 2 (Ltilde d.radical u))
    (hnP : Q d.radical t ≤ normalizer (componentSylowSeed d.radical u P : Set (FreeAmalgam d.radical)))
    (hs : componentSylowSeed d.radical u P ≤ sourceStarAlpha d.radical Y)
    (he : ¬ Z d.radical z ≤ normalizer
      ((componentSylowSeed d.radical u P ⊔ Z d.radical (alpha d.radical) :
        Subgroup (FreeAmalgam d.radical)) : Set _)) : False := by
  let E := Z d.radical z ⊓ Q d.radical (alpha d.radical)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases hh' : color d.radical t <;> simp_all
  have hEQ : E ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)
  have hEU : E ≤ stabilizer d.radical u := hEQ.trans (fun _ hx => hx.2 u (adjacent_symm _ hut))
  have hEN : E ≤ normalizer (componentSylowSeed d.radical u P : Set (FreeAmalgam d.radical)) :=
    hEQ.trans hnP
  let : IsElementaryAbelian 2 (Z d.radical z) := geometry.Z_elementary hb z path.end_color
  have hEsquare : ∀ x ∈ E, x*x=1 := by
    intro x hx
    have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (Z d.radical z)) ⟨x,hx.1⟩
    have hx2 : x ^ 2 = 1 := congrArg Subtype.val hh
    simpa only [pow_two] using hx2
  have hup := h.replacement_elementary_seed_index_le_degree d hu P E hEU hEN hEsquare
  have hYS := hs.trans (h.replacement_sourceStarAlpha_le_critical_endpoint_stabilizer
    d geometry hb path Y P₀ hY hn)
  have hYQ := hs.trans (h.replacement_sourceStarAlpha_le_own_core d geometry hb Y P₀ hY hn)
  have hlo := h.replacement_seed_actor_centralizer_index_ge_field d path hb
    (componentSylowSeed d.radical u P) hYS hYQ he
    (componentSylowSeed d.radical u P) le_rfl hYS
  change Nat.card F ≤ (centralizer (componentSylowSeed d.radical u P :
    Set (FreeAmalgam d.radical))).relIndex E at hlo
  rw [h.field_card] at hlo
  have hlt := n.lt_two_pow_self
  omega

/-- The first star commutator comparison of MS93 (3.4), on the actual
minimum characteristic replacement and at every nonbinary field degree. -/
theorem Input.replacement_sourceStarAlpha_commutator_le_Z
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical))) :
    ⁅sourceStarAlpha d.radical Y,Ltilde d.radical (alpha d.radical)⁆ ≤
      Z d.radical (alpha d.radical) := by
  by_contra hbad
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := d.radical) (geometry := geometry)
    (a := alpha d.radical) rfl
  obtain ⟨u,t,P',hu,hat,hut,hnP,hs,he⟩ :=
    h.replacement_bad_star_critical_seed d geometry hb path Y P hY hn hbad
  exact h.replacement_no_escaping_star_seed d geometry hb path Y P hY hn hu hat hut P' hnP hs he

/-- Coprime residual idempotence sharpens the first star bound to the literal
moving natural cover; the full fixed part is not removed from that cover. -/
theorem Input.replacement_sourceStarAlpha_commutator_le_U
    (geometry : Geometry d.radical) (hb : 0 < geometry.b d.radical)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical))) :
    ⁅sourceStarAlpha d.radical Y,Ltilde d.radical (alpha d.radical)⁆ ≤
      U d.radical (alpha d.radical) := by
  let S := stabilizer d.radical (alpha d.radical)
  let A := (sourceStarAlpha d.radical Y).subgroupOf S
  let : Finite S := finite_stabilizer d.radical (alpha d.radical)
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sourceStarAlpha_normalized d.radical Y)
  have hPQ : IsPGroup 2 (Q d.radical (alpha d.radical)) := by
    rw [Q_alpha d.radical (h.replacement_two_group d) (h.replacement_core_le d)]
    exact pCore_isPGroup.map _
  have hPA : IsPGroup 2 A := (hPQ.to_le
    (h.replacement_sourceStarAlpha_le_own_core d geometry hb Y P hY hn)).comap_subtype
  have hi := commutator_isPPerfect_idempotent (pResidual 2 S) A
    (isPPerfect_pResidual 2) hPA le_normalizer_of_normal
  have hmap := congrArg (Subgroup.map S.subtype) hi
  have hAm : A.map S.subtype = sourceStarAlpha d.radical Y :=
    map_subgroupOf_eq_of_le (sourceStarAlpha_le_stabilizer d.radical Y)
  simp only [map_commutator,hAm] at hmap
  change ⁅⁅sourceStarAlpha d.radical Y,Ltilde d.radical (alpha d.radical)⁆,
    Ltilde d.radical (alpha d.radical)⁆ =
    ⁅sourceStarAlpha d.radical Y,Ltilde d.radical (alpha d.radical)⁆ at hmap
  rw [←hmap]
  exact commutator_mono (h.replacement_sourceStarAlpha_commutator_le_Z d geometry hb Y P hY hn) le_rfl

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
