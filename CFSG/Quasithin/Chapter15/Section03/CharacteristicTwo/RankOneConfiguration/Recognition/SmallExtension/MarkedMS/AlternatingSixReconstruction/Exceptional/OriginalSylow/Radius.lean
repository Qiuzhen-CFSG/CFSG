module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.SmallShiftDichotomy
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadius
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadius
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration

/-!
# Radius alternatives for the original Borel geometry

If the full omega layer is not centrally generated, one trapped critical
radius forces every adjacent Baumann slice to have index at most two.
Indeed, a strict slice would give one of the paired backward paths. The
actual component switch preserves the trapped radius, so either new path
would have its seed inside its endpoint core, contradicting criticality.

The predecessor-slice theorem then identifies the full reverse critical
kernel and gives order two for both critical images. Conversely, one large
critical image or one strict adjacent slice forces every critical radius to
escape. The same radius escape produces backward walks with every overlap,
and iterating and reversing them gives a reverse prefix and forward
eligibility for every critical path.

The final theorem discharges the conditional path premises by separating
central generation, universal radius escape, and uniformly small slices.
Central generation and uniformly small slices remain alternatives, not
contradictions. Forward eligibility is not a strict-slice estimate. The
terminal exclusions and whole-core reconstruction remain open. Both full
covers and the original projection kernel E, including E/Q of order three,
are retained.

The internal imports reuse only the generic critical-kernel and path
transport lemmas from CubicPlaneRadius, together with omega transport.
No plane-image theorem or natural replacement is used for the Borel graph.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.7)--(5.8), printed pp.919--920; Aschbacher--Smith C.1.31--32,
printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem borel_radius_failure_base_slices
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (hn : X Rg (alpha Rg) ≠ U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    {z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hbad : V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    {c t : Vertex Rg} (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t) :
    (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2 := by
  have hb := distance_gt_two h e hz hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 := by
    by_contra! hh
    exact large_critical_radius_escape h e hz hk p hh hbad
  by_contra! hstrict
  have ha1 : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨k,hkG,hkt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hat ha1
  have hkfix : act Rg k (alpha Rg) = alpha Rg := hkG
  have hdelta : Adjacent Rg (act Rg k c) (p.walk.getVert 1) := by
    rw [←hkt]
    exact (adjacent_act_iff Rg k _ _).mpr hct
  have hBs := Escape.PairingControl.FirstPairing.B_act
    (geometry := sourceGeometry h) hb k (alpha Rg) rfl
  rw [hkfix] at hBs
  have hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg k c)) := by
    rw [U_act,hBs,relIndex_map_map_of_injective _ _ (MulAut.conj k⁻¹).injective]
    exact hstrict
  rcases borel_small_shift_or_central_generation h e hz hk u hR p hp hdelta hs with
    hcentral | hpaths
  · exact hn (hcentral _ rfl).1
  obtain ⟨s,has,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,g,hg,hgt,hindex,halt⟩ := hpaths
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hqbad : V Rg (alpha Rg) ≤ Q Rg (q.walk.getVert (q.walk.length-2)) := by
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    rw [hlen,hqverts,Q_act]
    have hV : (V Rg (alpha Rg)).map (MulAut.conj x⁻¹).toMonoidHom =
        V Rg (alpha Rg) := mem_normalizer_iff_map_conj_eq.mp
      (DistanceEight.V_normalized Rg _ ((stabilizer Rg (alpha Rg)).inv_mem hx))
    rw [←hV]
    exact map_mono hbad
  have hcs : Adjacent Rg (act Rg g (act Rg k c)) s := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hdelta
  have hdist : (cosetGraph Rg).dist (act Rg g (act Rg k c)) (alpha Rg) ≤ 2 :=
    CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two has hcs
  have hZV : Z Rg (act Rg g (act Rg k c)) ≤ V Rg (alpha Rg) :=
    (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)
  rcases halt with ⟨b,_,_⟩ | ⟨b,_,_⟩
  · exact b.critical.2 (hZV.trans hbad)
  · exact b.critical.2 (hZV.trans hqbad)

include h e hz hk in
/-- A trapped Borel radius and failure of full omega central generation
force every two-edge Baumann slice to have index at most two. The same selected switch transports
radius containment to the paired path, excluding both backward alternatives. -/
theorem borel_radius_failure_uniform_slices
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (hn : X Rg (alpha Rg) ≠ U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hbad : V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    {v c t : Vertex Rg} (hv : color Rg v = false)
    (hvt : Adjacent Rg v t) (hct : Adjacent Rg c t) :
    (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2 := by
  have hb := distance_gt_two h e hz hk
  obtain ⟨f,hf⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg f⁻¹ a = alpha Rg := by
    rw [hf,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg f⁻¹ a) (act Rg f⁻¹ z),
      (∀ i, p₀.walk.getVert i = act Rg f⁻¹ (p.walk.getVert i)) ∧
      p₀.walk.length = p.walk.length :=
    ⟨p.act f⁻¹,fun i => by simp only [CriticalPath.act,actWalk_getVert],
      actWalk_length Rg f⁻¹ p.walk⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hverts,hlen⟩ := hpact
  have hbad₀ : V Rg (alpha Rg) ≤ Q Rg (p₀.walk.getVert (p₀.walk.length-2)) := by
    rw [hlen,hverts,←hbase,V_act,Q_act]
    exact map_mono hbad
  obtain ⟨g,hgv⟩ := exists_mVertex_of_color Rg hv
  have hgvbase : act Rg g⁻¹ v = alpha Rg := by
    rw [hgv,act_mVertex,mul_inv_cancel]
    rfl
  have hgt : Adjacent Rg (alpha Rg) (act Rg g⁻¹ t) := by
    rw [←hgvbase]
    exact (adjacent_act_iff Rg g⁻¹ _ _).mpr hvt
  have hh := borel_radius_failure_base_slices h e hz hk u hR hn p₀ hbad₀ hgt
    ((adjacent_act_iff Rg g⁻¹ _ _).mpr hct)
  rw [←hgvbase,Escape.PairingControl.FirstPairing.B_act
    (geometry := sourceGeometry h) hb g⁻¹ v hv,U_act,
    relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective] at hh
  exact hh

include h e hz hk in
/-- When central generation fails, a trapped Borel radius forces the full
reverse-kernel identity and both order-two critical images on every path. -/
theorem borel_radius_failure_critical_kernels
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (hn : X Rg (alpha Rg) ≠ U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hbad : V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    {c c' : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) c c') :
    Z Rg c' ⊓ B Rg (q.walk.getVert (q.walk.length-2))
        ((sourceGeometry h).Z_normal _) = Z Rg c' ⊓ Q Rg c ∧
      (Q Rg c).relIndex (Z Rg c') = 2 ∧
      (Q Rg c').relIndex (Z Rg c) = 2 := by
  exact critical_kernel_of_uniform_slices h e hz hk
    (fun _ _ _ hv hvt hct =>
      borel_radius_failure_uniform_slices h e hz hk u hR hn p hbad hv hvt hct) q

include h e hz hk in
/-- When central generation fails, one large critical image forces every
critical radius to escape, including paths with small critical images. -/
theorem borel_radius_escape_of_large_pair
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (hn : X Rg (alpha Rg) ≠ U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg a))
    {c c' : Vertex Rg} (q : CriticalPath Rg (sourceGeometry h) c c') :
    ¬ V Rg c ≤ Q Rg (q.walk.getVert (q.walk.length-2)) := by
  intro hbad
  have hh := (borel_radius_failure_critical_kernels h e hz hk u hR hn q hbad p).2.2
  omega

include h e hz hk in
/-- When central generation fails, one strict two-edge slice forces radius
escape on every critical path, with no restriction on its image size. -/
theorem borel_radius_escape_of_strict_slice
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (hn : X Rg (alpha Rg) ≠ U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    {v c t : Vertex Rg} (hv : color Rg v = false)
    (hvt : Adjacent Rg v t) (hct : Adjacent Rg c t)
    (hs : 2 < (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c))
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    ¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  exact (Nat.not_le_of_gt hs)
    (borel_radius_failure_uniform_slices h e hz hk u hR hn p hbad hv hvt hct)

include h e hz hk in
/-- When central generation fails, a large critical witness or strict slice
gives backward paths at every component vertex, with the entire overlap. Iterating those very paths
also gives a reverse prefix and forward eligibility for every critical path. -/
theorem borel_paths_of_large_pair_or_strict_slice
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (hn : X Rg (alpha Rg) ≠ U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    (hwitness : (∃ a z, ∃ _p : CriticalPath Rg (sourceGeometry h) a z,
        4 ≤ (Q Rg z).relIndex (Z Rg a)) ∨
      (∃ v c t : Vertex Rg, color Rg v = false ∧ Adjacent Rg v t ∧ Adjacent Rg c t ∧
        2 < (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)))
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    (¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∧
    (∃ d, ∃ w : (cosetGraph Rg).Walk d a,
      ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
        w.length = 2 ∧ q.walk = w.append (p.walk.take (p.walk.length-2)) ∧
        ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
    (∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) d,
      q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = a) ∧
    ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
  have hb := distance_gt_two h e hz hk
  have escape : ∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
      ¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    intro a z p
    rcases hwitness with ⟨a₀,z₀,p₀,hlarge⟩ | ⟨v,c,t,hv,hvt,hct,hs⟩
    · exact borel_radius_escape_of_large_pair h e hz hk u hR hn p₀ hlarge p
    · exact borel_radius_escape_of_strict_slice h e hz hk u hR hn hv hvt hct hs p
  have hprefix := reverse_prefix_of_radius_escape h e hb escape p
  refine ⟨escape _ _ p,backward_path_of_radius_escape h p (escape _ _ p) hb,hprefix,?_⟩
  obtain ⟨d,q,_,hqa⟩ := hprefix
  have hh := critical_start_not_le_second_slice h e hz hb q
  rwa [hqa] at hh

include h e hz hk in
/-- The surviving Borel geometry has full omega central generation, or
compatible forward and backward critical paths at every component vertex,
or uniformly small slices with exact full critical kernels. No path or
strict-slice premise is added. -/
theorem borel_radius_alternatives
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    (∀ a : Vertex Rg, color Rg a = false →
      (X Rg a = U Rg a ⊔
        (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) ∧
      X Rg a = Z Rg a) ∨
    (∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
      (¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∧
      (∃ d, ∃ w : (cosetGraph Rg).Walk d a,
        ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
          w.length = 2 ∧ q.walk = w.append (p.walk.take (p.walk.length-2)) ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      (∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) d,
        q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = a) ∧
      ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _)) ∨
    ((∀ v c t : Vertex Rg, color Rg v = false → Adjacent Rg v t → Adjacent Rg c t →
      (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2) ∧
      ∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
        Z Rg z ⊓ B Rg (p.walk.getVert (p.walk.length-2))
            ((sourceGeometry h).Z_normal _) = Z Rg z ⊓ Q Rg a ∧
          (Q Rg a).relIndex (Z Rg z) = 2 ∧
          (Q Rg z).relIndex (Z Rg a) = 2) := by
  classical
  by_cases hn : X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)))
  · apply Or.inl
    intro a ha
    have hh := omega_generation_transport (show color Rg (alpha Rg) = false from rfl) ha hn
    exact ⟨hh,omega_eq_seed_of_central_generation h a ha hh⟩
  right
  by_cases hw : (∃ a z, ∃ _p : CriticalPath Rg (sourceGeometry h) a z,
      4 ≤ (Q Rg z).relIndex (Z Rg a)) ∨
    (∃ v c t : Vertex Rg, color Rg v = false ∧ Adjacent Rg v t ∧ Adjacent Rg c t ∧
      2 < (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c))
  · exact Or.inl (fun _ _ p => borel_paths_of_large_pair_or_strict_slice h e hz hk u hR hn hw p)
  · have hall : ∀ v c t : Vertex Rg, color Rg v = false → Adjacent Rg v t → Adjacent Rg c t →
        (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2 := by
      intro v c t hv hvt hct
      by_contra! hh
      exact hw (Or.inr ⟨v,c,t,hv,hvt,hct,hh⟩)
    exact Or.inr ⟨hall,fun _ _ p => critical_kernel_of_uniform_slices h e hz hk hall p⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
