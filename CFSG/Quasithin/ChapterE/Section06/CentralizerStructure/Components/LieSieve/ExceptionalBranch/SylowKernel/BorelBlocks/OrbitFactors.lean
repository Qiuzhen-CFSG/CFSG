module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks.Overgroup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks.OrbitFactors.Coordinates
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks.OrbitFactors.Seed

/-!
# Extracting an exceptional Borel from a subnormal A₃ block

For an A₅ component L of C, let B be the embedded normalizer of a Sylow
four-group S with image L ∩ Q. The component stabilizer in Q normalizes B.
The orbit of B therefore has actual direct-product coordinates, and every
short subgroup of BQ embeds into that orbit. Its irreducible commutator
module isolates a coordinate, yielding a Q-conjugate of B inside the block.

The proof retains relative subnormality in BQ and the original ambient
embeddings. Neither normalization of L by all of Q nor an identification
of the given block with A₄ is assumed. The A₄ seed facts are proved from
concrete five-point stabilizers.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7–8,
printed pp.246–248 (PDF pp.257–259), with C.1.7 and C.1.12–13. This is the
intrinsic factor-extraction helper; the E.6.8 witness assembly is separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks
variable {G : Type*} [Group G] [Finite G]

/-- A subnormal A₃ block in the full Borel-orbit overgroup contains a
Q-conjugate of the actual embedded Sylow normalizer. -/
theorem exists_conjugate_borel_le {C L Q : Subgroup G}
    (hL : ComponentIn C L) (hm : ClassicalGroup.IsPSL L 2 4)
    (hQC : Q ≤ C) (hQ : IsPGroup 2 Q) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (D : Subgroup G)
    (hDX : D ≤ (normalizer (S : Set L)).map L.subtype ⊔ Q)
    (hs : (D.subgroupOf ((normalizer (S : Set L)).map L.subtype ⊔ Q)).IsSubnormal)
    (hD : ChapterC.IsAlternatingBlock D 3) :
    ∃ q : G, q ∈ Q ∧
      ((normalizer (S : Set L)).map L.subtype).map (MulAut.conj q).toMonoidHom ≤ D := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let eL := e.trans eA
  let B := (normalizer (S : Set L)).map L.subtype
  let B' := B.subgroupOf C
  let Q' := Q.subgroupOf C
  let X := B ⊔ Q
  let X' := B' ⊔ Q'
  have hBL : B ≤ L := map_subtype_le _
  have hBC : B ≤ C := hBL.trans hL.1
  have hmB : B'.map C.subtype = B := map_subgroupOf_eq_of_le hBC
  have hmQ : Q'.map C.subtype = Q := map_subgroupOf_eq_of_le hQC
  have hmX : X'.map C.subtype = X := by rw [Subgroup.map_sup, hmB, hmQ]
  let eX : X' ≃* X := (equivMapOfInjective X' C.subtype C.subtype_injective).trans
    (MulEquiv.subgroupCongr hmX)
  let f : D →* X' := eX.symm.toMonoidHom.comp (inclusion hDX)
  have hf : Function.Injective f := eX.symm.injective.comp (inclusion_injective hDX)
  have hsf : f.range.IsSubnormal := by
    rw [MonoidHom.range_comp, inclusion_range]
    exact hs.map eX.symm.surjective
  have hZ : center (L.subgroupOf C) = ⊥ := by
    let t := (subgroupOfEquivOfLe hL.1).trans eL
    apply eq_bot_iff.mpr
    intro x hx
    have ht : t x ∈ center (alternatingGroup (Fin 5)) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z, rfl⟩ := t.surjective y
      simpa only [map_mul] using congrArg t (mem_center_iff.mp hx z)
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at ht
    exact mem_bot.mpr (t.injective (ht.trans t.map_one.symm))
  have hn : Q' ⊓ normalizer (L.subgroupOf C : Set C) ≤ normalizer (B' : Set C) := by
    rw [← subgroupOf_normalizer_eq hL.1, ← subgroupOf_normalizer_eq hBC]
    exact fun _ hx => stabilizer_normalizes S hS hx
  let eB : B' ≃* normalizer (S : Set L) :=
    (subgroupOfEquivOfLe hBC).trans
      (equivMapOfInjective (normalizer (S : Set L)) L.subtype L.subtype_injective).symm
  obtain ⟨hB, hBZ, P, hPN, hPS, hP, hPn, hPc⟩ :=
    OrbitFactors.normalizer_seed_properties eL S eB
  let := hPN
  let := hPS
  obtain ⟨q, hq⟩ := OrbitFactors.local_short_factor hL.2 hZ
    (subgroupOf_mono C hBL) hn hQ.comap_subtype hB hBZ P hP hPn hPc hD.2.1 f hf hsf
  have hhom : C.subtype.comp (X'.subtype.comp f) = D.subtype := by
    ext d
    have he := eX.apply_symm_apply (inclusion hDX d)
    exact congrArg Subtype.val he
  have hmD : (f.range.map X'.subtype).map C.subtype = D := by
    rw [← MonoidHom.range_comp, ← MonoidHom.range_comp, hhom,
      range_subtype]
  refine ⟨(q : C), q.property, ?_⟩
  rintro x ⟨b, hb, rfl⟩
  have hb' : (⟨b, hBC hb⟩ : C) ∈ B' := hb
  have hh := hq (mem_map_of_mem (MulAut.conj (q : C)).toMonoidHom hb')
  have hh' := mem_map_of_mem C.subtype hh
  rw [hmD] at hh'
  exact hh'

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks
end
