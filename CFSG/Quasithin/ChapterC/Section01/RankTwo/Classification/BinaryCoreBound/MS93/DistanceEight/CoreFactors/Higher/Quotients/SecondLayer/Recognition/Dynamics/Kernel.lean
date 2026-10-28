module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Actions
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# Dynamics on the literal orbit quotient

Trivial conjugation modulo the denominator makes the seed commutator with
the second layer invariant under the local group, because the denominator
centralizes that layer. Thus a noninvariant commutator excludes the whole
action kernel; simplicity of the original SL3(2) excludes every other kernel.
The separate generation lemma sends the saturated ambient commutator equality
to full movement on the literal relative quotient.

These are transfer lemmas, not assumptions of faithfulness or new action data.
`first_factor_faithful` supplies the first actual source application.
Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iii), printed p.899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition

variable {G : Type*} [Group G]
private theorem normalized_commutator (A B P N : Subgroup G)
    (hA : P ≤ normalizer A) (hB : ⁅B,P⁆ ≤ N)
    (hN : N ≤ centralizer (A : Set G)) : P ≤ normalizer (⁅A,B⁆ : Subgroup G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  have hm : (⁅A,B⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ ⁅A,B⁆ := by
    rw [map_commutator, MulEquiv.toMonoidHom_eq_coe, mem_normalizer_iff_map_conj_eq.mp (hA hg)]
    apply commutator_le.mpr
    rintro a ha _ ⟨b, hb, rfl⟩
    have hn : b⁻¹ * g * b * g⁻¹ ∈ N := by
      simpa only [commutatorElement_def, inv_inv] using
        hB (commutator_mem_commutator (B.inv_mem hb) hg)
    have hc : ⁅a, b⁻¹ * g * b * g⁻¹⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hN hn a ha)
    have he : (MulAut.conj g) b = b * (b⁻¹ * g * b * g⁻¹) := by
      simp [mul_assoc]
    change ⁅a, (MulAut.conj g) b⁆ ∈ ⁅A,B⁆
    rw [he, commutatorElement_mul_right_eq_mul_conj, hc]
    simpa using commutator_mem_commutator ha hb
  exact hm (mem_map_of_mem _ hx)

open NormalizerTransfer
variable {M : Type*} [Group M] {R L : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R}

/-- The source centralizer argument, on any actual orbit factor. If its action
were trivial, its seed would move only inside the common denominator. Since
that denominator centralizes the second layer, the seed commutator would be
normalized by the whole local group. Simplicity excludes every other kernel. -/
theorem OrbitModule.faithful_of_not_normalized_commutator
    (earlier : Earlier R geometry) {p : Higher.SourcePath (alpha R)}
    {v : Vertex R} (s : OrbitModule source p v)
    (hbad : ¬ stabilizer R (alpha R) ≤ normalizer
      (⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Z R v⁆ :
        Subgroup (FreeAmalgam R))) :
    let := s.normal; Function.Injective s.action := by
  let := s.normal
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  rcases (inferInstance : s.action.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact s.action.ker_eq_bot_iff.mp hb
  exfalso
  have hone : s.action = 1 := MonoidHom.ker_eq_top_iff.mp ht
  apply hbad
  apply normalized_commutator _ _ _
    (hatV R (alpha R) (p.walk.getVert 6)) (hatW_normalized R _ _ _)
    ?_ (denominator_centralizes_second earlier p)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro g hg z hz
  have hgM : g ∈ Mbar R := by simpa only [alpha, stabilizer_m_base] using hg
  obtain ⟨m, rfl⟩ := hgM
  have hx : z ∈ orbitFactor p v :=
    (show conjugatesIn (Z R v) (stabilizer R (alpha R)) ≤ orbitFactor p v from le_sup_left)
      (Escape.Initial.Natural.conjugatesIn_contains (Z R v) (stabilizer R (alpha R)) hz)
  let x : orbitFactor p v := ⟨z, hx⟩
  let y : orbitFactor p v := ⟨embedM R m * z * (embedM R m)⁻¹,
    le_normalizer_iff.mp (orbitFactor_normalized p v) _ hg _ hx⟩
  have hq := s.conjugation m x y rfl
  rw [hone] at hq
  have hn := QuotientGroup.eq_iff_div_mem.mp hq.symm
  change embedM R m * z * (embedM R m)⁻¹ / z ∈ hatV R (alpha R) (p.walk.getVert 6) at hn
  simpa only [commutatorElement_def, div_eq_mul_inv] using hn

/-- Descend the saturated source equality through the exact recorded action.
This is the quotient step only: the ambient generation equality remains to
be proved by the source moving-generation argument. -/
theorem OrbitModule.full_of_generation {p : Higher.SourcePath (alpha R)}
    {v : Vertex R} (s : OrbitModule source p v)
    (hgen : ⁅orbitFactor p v, stabilizer R (alpha R)⁆ ⊔
      hatV R (alpha R) (p.walk.getVert 6) = orbitFactor p v) :
    letI := s.normal; commutatorAction s.action.range (OrbitSpace p v) = ⊤ := by
  let := s.normal
  let A := orbitFactor p v
  let N := hatV R (alpha R) (p.walk.getVert 6)
  let π := QuotientGroup.mk' (N.subgroupOf A)
  let C := commutatorAction s.action.range (OrbitSpace p v)
  let D := (C.comap π).map A.subtype
  have hcomm : ⁅A, stabilizer R (alpha R)⁆ ≤ D := by
    apply commutator_le.mpr
    intro x hx g hg
    have hgM : g ∈ Mbar R := by simpa only [alpha, stabilizer_m_base] using hg
    obtain ⟨m, rfl⟩ := hgM
    let u : A := ⟨x, hx⟩
    let y : A := ⟨embedM R m * (x⁻¹) * (embedM R m)⁻¹,
      le_normalizer_iff.mp (orbitFactor_normalized p v) _ hg _ (A.inv_mem hx)⟩
    let actor : s.action.range := ⟨s.action (source.projection m),
      ⟨source.projection m, rfl⟩⟩
    have hmem : (π u⁻¹)⁻¹ * (actor • π u⁻¹) ∈ C := by
      dsimp only [C]
      rw [commutatorAction_eq_closure]
      exact subset_closure ⟨actor, π u⁻¹, rfl⟩
    change (π u⁻¹)⁻¹ * s.action (source.projection m) (π u⁻¹) ∈ C at hmem
    have hy := s.conjugation m u⁻¹ y rfl
    change s.action (source.projection m) (π u⁻¹) = π y at hy
    rw [hy, ← map_inv, ← map_mul] at hmem
    refine ⟨(u⁻¹)⁻¹ * y, hmem, ?_⟩
    change (x⁻¹)⁻¹ * (embedM R m * x⁻¹ * (embedM R m)⁻¹) = ⁅x, embedM R m⁆
    simp only [inv_inv, commutatorElement_def, mul_assoc]
  have hN : N ≤ D := by
    intro x hx
    let u : A := ⟨x, denominator_le p v hx⟩
    refine ⟨u, ?_, rfl⟩
    change π u ∈ C
    have hu : π u = 1 := (QuotientGroup.eq_one_iff u).mpr hx
    rw [hu]
    exact C.one_mem
  have hAD : A ≤ D := hgen.ge.trans (sup_le hcomm hN)
  apply top_unique
  intro z _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf A) z
  obtain ⟨y, hy, he⟩ := hAD x.property
  have he' : y = x := Subtype.ext he
  exact he' ▸ hy

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition
