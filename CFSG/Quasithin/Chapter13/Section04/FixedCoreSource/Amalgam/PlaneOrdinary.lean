module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.PlaneMarking
public import Theory.SpecificGroups.SymmetricSix.Parabolics
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# The original plane parabolic forces the ordinary alternating quotient

The T-invariant natural plane aligns with the canonical syntheme plane
under the literal L/O₂,Z(L) marking. Its inner normalizer therefore maps
onto the alternating syntheme stabilizer of order 24. The full normalizer
has S₃ two-core quotient, so its order has three-part exactly three.
The kernel of the inner map is consequently a two-group and contains the
whole marking kernel O₂,Z(L). Thus O₂,Z(L)=O₂(L), giving the actual ordinary
A₆ quotient without an assumed ordinary-row marking.

ModelSelection uses this to discharge the original-L marking in the
nonsolvable plane conclusion. This also excludes a covered original L
for every plane admitted by PlaneAmalgamSource1347.
Source: Aschbacher--Smith Notation 13.2.1 and Proposition 13.4.7(3--4),
printed pp.877,899--903; the relative normalizer is N_LT(V₂).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V B : Subgroup G}

/-- The actual S₃ plane normalizer removes the central covering kernel of L. -/
theorem original_plane_ordinary
    (D : ChosenModule T L V) (m : CoreMarking D)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨g,hg⟩ := m.natural_plane_alignment W hW hTW
  let J := L ⊓ normalizer (m.naturalPreimage W : Set G)
  have hJL : J ≤ L := inf_le_left
  have hJB : J ≤ B := by
    rw [hB]
    exact inf_le_inf_right _ le_sup_left
  have himage := m.aligned_inner_plane_image W g hg
  let q : L →* alternatingGroup (Fin 6) :=
    (m.relabel g).quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hmem (j : J) : q (inclusion hJL j) ∈ a6SynthemeStabilizer := by
    have hh : (q (inclusion hJL j)).val ∈ synthemeStabilizer ⊓ alternatingGroup (Fin 6) := by
      rw [←himage]
      exact mem_map_of_mem _ j.property
    exact hh.1
  let f : J →* a6SynthemeStabilizer := (q.comp (inclusion hJL)).codRestrict _ hmem
  have hf : Function.Surjective f := by
    intro a
    have hh : a.val.val ∈ synthemeStabilizer ⊓ alternatingGroup (Fin 6) :=
      ⟨a.property,a.val.property⟩
    rw [←himage] at hh
    obtain ⟨l,hl,he⟩ := hh
    exact ⟨⟨l.val,hl⟩,Subtype.ext (Subtype.ext he)⟩
  have hcardJ : Nat.card J = 24 * Nat.card f.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv,
      a6SynthemeStabilizer_order]
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
  have hd : 24 * Nat.card f.ker ∣ 6 * 2 ^ n := by
    rw [←hcardJ,←hn,←SymmetricThreeTwoCore.card_eq eB]
    exact card_dvd_of_le hJB
  have hk : IsPGroup 2 f.ker := by
    apply IsPGroup.of_card_dvd_pow (n := n)
    obtain ⟨k,hk⟩ := hd
    exact ⟨4 * k,by nlinarith [hk]⟩
  let j : centralCore L →* J :=
    (L.subtype.comp (centralCore L).subtype).codRestrict _ (by
      intro c
      refine ⟨c.val.property,(m.normalizes_naturalPreimage_iff W c.val).mpr ?_⟩
      have hc : QuotientGroup.mk' (centralCore L) c.val = 1 :=
        (QuotientGroup.eq_one_iff c.val).mpr c.property
      rw [hc,map_one]
      exact one_mem _)
  let i : centralCore L →* f.ker := j.codRestrict _ (by
    intro c
    change f (j c) = 1
    apply Subtype.ext
    change (m.relabel g).quotient (QuotientGroup.mk' (centralCore L) c.val) = 1
    have hq : QuotientGroup.mk' (centralCore L) c.val = 1 :=
      (QuotientGroup.eq_one_iff c.val).mpr c.property
    rw [hq,map_one])
  have hi : Function.Injective i := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : f.ker => c.val.val) hab
  have hc : IsPGroup 2 (centralCore L) := hk.of_injective i hi
  have he : centralCore L = pCore 2 L := by
    refine le_antisymm ?_ ?_
    · exact le_sSup ⟨inferInstance,hc⟩
    · intro l hl
      change QuotientGroup.mk' (pCore 2 L) l ∈ center (L ⧸ pCore 2 L)
      have hq : QuotientGroup.mk' (pCore 2 L) l = 1 :=
        (QuotientGroup.eq_one_iff l).mpr hl
      rw [hq]
      exact one_mem _
  exact ⟨(QuotientGroup.quotientMulEquivOfEq he.symm).trans m.quotient⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
