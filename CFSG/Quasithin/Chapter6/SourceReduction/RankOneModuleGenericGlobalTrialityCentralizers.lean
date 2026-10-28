module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityMaximal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Centralizers
public import Theory.SpecificGroups.Triality.NormalizedRootCentralizers

/-!
# Ambient central-involution bounds for the triality completion

In the genuine graph-field triality model, an element central in the arms
factor centralizes its root radical. The full parabolic radical-centralizer
bound puts it in that radical, hence in its highest-root center. The actual
fixed torus scales the highest-root parameter by every nonzero base-field
element. This proves transitivity on the nonidentity center and transports
through the original compatible parabolic map to K = O²(H).

Characteristic two puts Z(K) inside the original Sylow T. The center is
T-invariant and therefore contains a central involution of T. The established
right maximality and uniqueness over KT bound its ambient centralizer by
N_G(K). The torus orbit transports this bound to every central involution
of K; original uniqueness over L supplies the other bound in 5.3.3.

The Chapter12 application combines these bounds with the literal normalizer
conditions, without additional action or centralizer premises. Preparation
still retains original uniqueness, and the compatible comparison remains
explicit. Exhaustive F.1.12 comparison and concrete and ambient completion
recognition remain with the generic-global owner. The original source S and
whole overlap are preserved, and no ambient model isomorphism is asserted.
Source: Aschbacher–Smith 5.3.1–3, printed pp.658–659, and F.1.12(I)(4),
pp.262–264 (`refs/quasithin.pdf`). Root conventions and their GLS references
are those of the genuine triality modules imported above.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
open Subgroup Theory.GroupTheory
open _root_.Triality.Standard Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open _root_.Triality.Standard.RadicalCoordinates.Centers
open _root_.Triality.Standard.NormalizedRootCentralizers

private theorem triality_center_mem_highestRoot (P : Parameters) (hp : P.prime = 2)
    {z : Carrier P} (hz : z ∈ (center (localFactor P .arms)).map (localFactor P .arms).subtype) :
    z ∈ highestRoot P := by
  obtain ⟨a,ha,rfl⟩ := hz
  have hc : a.val ∈ centralizer (radical P .arms : Set (Carrier P)) := by
    apply mem_centralizer_iff.mpr
    intro r hr
    exact congrArg Subtype.val
      (mem_center_iff.mp ha ⟨r,radical_le_localFactor P hp .arms hr⟩)
  have har : a.val ∈ radical P .arms :=
    parabolic_centralizer_radical_le P hp .arms ⟨localFactor_le_parabolic P .arms a.property,hc⟩
  rw [←RadicalCoordinates.embedded_center_radical_arms P hp]
  refine ⟨⟨a.val,har⟩,mem_center_iff.mpr (fun r => ?_),rfl⟩
  apply Subtype.ext
  exact congrArg (fun k : localFactor P .arms => (k : Carrier P))
    (mem_center_iff.mp ha ⟨r,radical_le_localFactor P hp .arms r.property⟩)

private theorem triality_highest_root_orbit (P : Parameters) (hp : P.prime = 2)
    (x y : Carrier P) (hx : x ∈ highestRoot P) (hy : y ∈ highestRoot P)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    ∃ g ∈ borel P, y = g*x*g⁻¹ := by
  rw [←highestHom_range P hp] at hx hy
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  have ha0 : a.toAdd ≠ 0 := by
    intro he
    apply hx1
    rw [show a = 1 from congrArg Multiplicative.ofAdd he, map_one]
  have hb0 : b.toAdd ≠ 0 := by
    intro he
    apply hy1
    rw [show b = 1 from congrArg Multiplicative.ofAdd he, map_one]
  let u : (fixedField P)ˣ := Units.mk0 (b.toAdd / a.toAdd) (div_ne_zero hb0 ha0)
  let g := TorusCoordinates.torusMulEquiv P hp (1,u)
  refine ⟨g,torus_le_borel P g.property,?_⟩
  change highestHom P hp b = g.val * highestHom P hp a * g.val⁻¹
  have hs := torus_conjugate_highestHom P hp (1,u) a.toAdd
  change g.val * highestHom P hp a * g.val⁻¹ =
    highestHom P hp (Multiplicative.ofAdd (u.val * a.toAdd)) at hs
  rw [hs]
  congr 1
  apply Multiplicative.toAdd.injective
  change b.toAdd = (b.toAdd / a.toAdd) * a.toAdd
  simp [ha0]

/-- The original right parabolic is transitive on the nonidentity center of
its factor, through the compatible triality comparison. -/
theorem Preparation.triality_right_center_orbit
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)) :
    ∀ x ∈ (center (residual H)).map (residual H).subtype, x ≠ 1 →
      ∀ y ∈ (center (residual H)).map (residual H).subtype, y ≠ 1 →
        ∃ g ∈ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
          y = g*x*g⁻¹ := by
  rcases he with he | he
  · exact (d.not_triality_arms_left_amalgam h hTH hp (binaryParameters m hm) rfl he).elim
  obtain ⟨e⟩ := he
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  have hKP : residual H ≤ P := le_sup_left.trans le_sup_left
  have hres : (residual H).subgroupOf P = solvableResidual P := by
    have hr : (solvableResidual P).map P.subtype = residual H :=
      d.parabolic_residuals h hTH hp 1
    rw [←hr]
    exact comap_map_eq_self_of_injective P.subtype_injective _
  apply center_orbit_transport (R := localFactor (binaryParameters m hm) .arms) hKP e.right
  · rw [hres,←map_map,map_solvableResidual_eq e.right.toMonoidHom e.right.surjective]
    exact TrialityComparison.arms_parabolic_residual (binaryParameters m hm) rfl
  · intro x hx hx1 y hy hy1
    obtain ⟨g,hg,he⟩ := triality_highest_root_orbit (binaryParameters m hm) rfl x y
      (triality_center_mem_highestRoot _ rfl hx) (triality_center_mem_highestRoot _ rfl hy) hx1 hy1
    exact ⟨g,borel_le_parabolic _ .arms hg,he⟩

/-- Both ambient central-involution bounds in source 5.3.3 for the actual
triality pair, with no additional center-action or centralizer hypothesis. -/
theorem Preparation.triality_central_involution_centralizers
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse)) :
    ∀ i : Fin 2, ∀ z ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype,
      orderOf z = 2 → centralizer ({z} : Set G) ≤ normalizer (![L,residual H] i : Set G) := by
  intro i
  fin_cases i
  · exact d.left_central_involution_centralizer
  have hTK := hH.1.1.2.trans (le_normalizer_residual H)
  have hK := d.triality_right_maximal h hH hp m hm he
  have hu := (Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.qtke T hK).normalizer_unique
  have ho : componentOrbit (residual H) (T : Subgroup G) = residual H :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hTK)
      (le_componentOrbit _ _)
  rw [ho] at hu
  have hc := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
    (h.qtke.evenCharacteristic T) hK.1
  have hPN : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ≤
      normalizer (residual H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show residual H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 from
        le_sup_left.trans le_sup_left)).mp ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 1)
  exact center_orbit_centralizer_bound hTK hc hPN hu
    (d.triality_right_center_orbit h hH.1.1.2 hp m hm he)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
