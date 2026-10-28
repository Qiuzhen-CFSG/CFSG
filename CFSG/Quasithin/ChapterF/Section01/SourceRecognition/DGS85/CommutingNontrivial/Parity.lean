module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.Neighborhood

/-!
# Opposite orbits for commuting critical centers

The Sylow-or-center alternative of 6.2(c) makes the final center central in
its local group. If the critical endpoints were conjugate, the first center
would be central too. An actual common edge Sylow would then put it in the
neighboring center span, contradicting escape at the minimum distance.
Thus the endpoints have opposite types and b is odd; b > 1 implies b >= 3.

Source: DGS, *Groups and Graphs* (1985), 3.8(d) and 8.1(a), pp.83,132--133.
The local groups and their Sylows remain explicit earlier-source data.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- A critical starting center cannot be central in a local group containing
an edge Sylow: it would lie in the neighboring Sylow-center span and fail
the critical escape. This is the 3.8(d) argument needed in 8.1(a). -/
theorem critical_start_not_central
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    {a beta a' : Vertex F} (hc : IsCriticalPair F a a')
    (hd : (graph F).dist beta a' < b F) (L : Subgroup G)
    (T : Sylow 2 (stabilizer F a)) (T' : Sylow 2 (stabilizer F beta))
    (hTT : (T : Subgroup (stabilizer F a)).map (stabilizer F a).subtype =
      (T' : Subgroup (stabilizer F beta)).map (stabilizer F beta).subtype)
    (hTL : (T : Subgroup (stabilizer F a)).map (stabilizer F a).subtype ≤ L) :
    ¬ Z F a ≤ omegaCenterIn L := by
  intro hcentral
  have hseed : Z F a ≤ omegaCenterIn
      ((T : Subgroup (stabilizer F a)).map (stabilizer F a).subtype) := by
    intro z hz
    refine (mem_omegaCenterIn_iff _ _).mpr ⟨?_, ?_, ?_⟩
    · exact pCoreIn_le_sylow (stabilizer F a) T
        ((map_subtype_le _) (hZ a hz))
    · exact centralizer_le hTL ((mem_omegaCenterIn_iff _ _).mp (hcentral hz)).2.1
    · exact ((mem_omegaCenterIn_iff _ _).mp (hZ a hz)).2.2
  rw [hTT] at hseed
  have hZbeta : Z F a ≤ Z F beta := hseed.trans
    (le_iSup (fun R : Sylow 2 (stabilizer F beta) =>
      omegaCenterIn ((R : Subgroup (stabilizer F beta)).map (stabilizer F beta).subtype)) T')
  exact hc.2 (hZbeta.trans (Z_le_U_of_dist_lt_b F beta a' hd))

/-- The literal 6.2(c) Sylow-or-center alternative forces the ending
center to be central when the critical centers commute. -/
theorem critical_end_center_of_commuting [∀ i, Finite (F i)]
    (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hQU : ∀ v, Q F v ≤ U F v)
    {a a' : Vertex F} (hc : IsCriticalPair F a a')
    (hcomm : ⁅Z F a, Z F a'⁆ = ⊥) (L : Subgroup G)
    (halt : (∃ T : Sylow 2 ↥(stabilizer F a' ⊓ centralizer (Z F a' : Set G) : Subgroup G),
      (T : Subgroup ↥(stabilizer F a' ⊓ centralizer (Z F a' : Set G) : Subgroup G)).map
        (stabilizer F a' ⊓ centralizer (Z F a' : Set G)).subtype = Q F a') ∨
      Z F a' = omegaCenterIn L) :
    Z F a' = omegaCenterIn L := by
  rcases halt with ⟨T, hT⟩ | h
  · have hZG := Z_le_stabilizer_of_dist_le_b F hgen a a' hc.1.le
    have hp : IsPGroup 2 (Z F a) :=
      (isPGroup_pCoreIn 2 (stabilizer F a)).to_le ((hZ a).trans (map_subtype_le _))
    have hZQ := le_sylow_image_of_normalizes
      (stabilizer F a' ⊓ centralizer (Z F a' : Set G)) T hT hp
      (le_inf hZG (commutator_eq_bot_iff_le_centralizer.mp hcomm))
      (hZG.trans (stabilizer_normalizes_Q F a'))
    exact (hc.2 (hZQ.trans (hQU a'))).elim
  · exact h

/-- Source 8.1(a): commuting critical centers give opposite vertex orbits,
an odd critical distance, and the actual central omega equality at beta.
Only the earlier 6.2(c) alternative and literal local/edge Sylow data are
inputs; oddness and the lower bound are proved. -/
theorem commuting_critical_parity [∀ i, Finite (F i)]
    (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hQU : ∀ v, Q F v ≤ U F v)
    (L : Vertex F → Subgroup G)
    (hLconj : ∀ g v, L (g • v) = (L v).map (MulAut.conj g).toMonoidHom)
    (hLSyl : ∀ v (T : Sylow 2 (stabilizer F v)),
      (T : Subgroup (stabilizer F v)).map (stabilizer F v).subtype ≤ L v)
    {a beta a' : Vertex F} (hc : IsCriticalPair F a a')
    (hab : (graph F).Adj a beta) (hd : (graph F).dist beta a' + 1 = b F)
    (hb : 1 < b F) (hcomm : ⁅Z F a, Z F a'⁆ = ⊥)
    (hedge : ∃ (T : Sylow 2 (stabilizer F a)) (T' : Sylow 2 (stabilizer F beta)),
      (T : Subgroup (stabilizer F a)).map (stabilizer F a).subtype =
        (T' : Subgroup (stabilizer F beta)).map (stabilizer F beta).subtype)
    (halt : (∃ T : Sylow 2 ↥(stabilizer F a' ⊓ centralizer (Z F a' : Set G) : Subgroup G),
      (T : Subgroup ↥(stabilizer F a' ⊓ centralizer (Z F a' : Set G) : Subgroup G)).map
        (stabilizer F a' ⊓ centralizer (Z F a' : Set G)).subtype = Q F a') ∨
      Z F a' = omegaCenterIn (L a')) :
    a.type ≠ a'.type ∧ Odd (b F) ∧ 3 ≤ b F ∧ Z F beta = omegaCenterIn (L beta) := by
  have hend := critical_end_center_of_commuting F hgen hZ hQU hc hcomm (L a') halt
  have htransport (v : Vertex F) (hv : a'.type = v.type) : Z F v = omegaCenterIn (L v) := by
    obtain ⟨g, hg⟩ := (same_orbit_iff F a' v).mpr hv
    rw [← hg, Z_translate, hLconj,
      ← NilesRankOneKernel.omegaCenterIn_map_injective _ (MulAut.conj g).injective, hend]
  have htypes : a.type ≠ a'.type := by
    intro he
    obtain ⟨T, T', hTT⟩ := hedge
    exact critical_start_not_central F hZ hc (by omega) (L a) T T' hTT
      (hLSyl a T) (htransport a he.symm).le
  have hodd : Odd (b F) := hc.1 ▸ (odd_dist_iff F hgen a a').mpr htypes
  have hbetatype : a'.type = beta.type := by
    have ht := hab.1
    cases ha : a.type <;> cases hbeta : beta.type <;> cases ha' : a'.type <;> simp_all
  refine ⟨htypes, hodd, ?_, htransport beta hbetatype⟩
  obtain ⟨n, hn⟩ := hodd
  omega


end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
