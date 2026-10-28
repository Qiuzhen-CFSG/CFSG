module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.Construction
public import Stellmacher.ElementaryAbelianMaxJ
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Transport of the ordinary A₇ marking to the six-point lift

A permutation realization agreeing with the original K/O₂(K) projection
transports the normalizer of the marked three-transposition subgroup to the
stabilizer of its unique fixed letter. Characteristicity of the Thompson
subgroup gives invariance of that stabilizer under the original two-group.
A transposition and a three-cycle give a nontrivial actor on the actual
residual lift, with nontriviality measured modulo its intrinsic two-core.

The marking and the local normalizer-residual identity are still source
obligations. These transport lemmas do not assert either of those statements.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, ordinary A₇ paragraph, printed p.932 (PDF p.949).
-/

@[expose] public section
open Subgroup Equiv Equiv.Perm Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement

variable {G : Type*} [Group G]

/-- The action image of a subgroup, with the ambient restriction retained. -/
def actionImage (H : Subgroup G) (ρ : H →* Perm (Fin 7)) (A : Subgroup G) :
    Subgroup (Perm (Fin 7)) := (A.subgroupOf H).map ρ

/-- Normalization passes through the specified action. -/
theorem actionImage_normalizer (H A : Subgroup G) (ρ : H →* Perm (Fin 7))
    (hA : A ≤ H) (g : H) (hg : (g : G) ∈ normalizer (A : Set G)) :
    ρ g ∈ normalizer (actionImage H ρ A : Set (Perm (Fin 7))) := by
  apply (A.subgroupOf H).le_normalizer_map ρ
  refine ⟨g, ?_, rfl⟩
  rw [← subgroupOf_normalizer_eq hA]
  exact hg

/-- The six-letter condition uses the original projection of the original k. -/
theorem mem_ambientPreimage (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (x : Fin 7) (k : K) :
    (k : G) ∈ ambientPreimage K e x ↔ (blockProjection K e k : Perm (Fin 7)) x = x := by
  unfold ambientPreimage
  change K.subtype k ∈ _ ↔ _
  rw [mem_map_iff_mem K.subtype_injective]
  exact mem_sixStabilizer_iff x _

/-- The source S-image marking places the literal relative normalizer in
our six-point preimage. No equality of normalizer images is required here. -/
theorem normalizer_le_preimage_of_marking (K H S : Subgroup G)
    (hK : K ≤ H) (hS : S ≤ H)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (ρ : H →* Perm (Fin 7))
    (hρ : ∀ k : K, ρ ⟨k, hK k.property⟩ = (blockProjection K e k : Perm (Fin 7)))
    (hmark : actionImage H ρ S = threeTranspositions) :
    K ⊓ normalizer (S : Set G) ≤ ambientPreimage K e 6 := by
  intro k hk
  apply (mem_ambientPreimage K e 6 ⟨k, hk.1⟩).mpr
  rw [← hρ]
  apply normalizer_threeTranspositions_fix_six
  rw [← hmark]
  exact actionImage_normalizer H S ρ hS ⟨k, hK hk.1⟩ hk.2

/-- The ambient two-group normalizes its elementary Thompson subgroup. -/
theorem normalizes_thompson (R : Subgroup G) :
    R ≤ normalizer (Stellmacher.elementaryAbelianMaxJ R : Set G) := by
  intro r hr
  rw [mem_normalizer_iff_map_conj_eq]
  change (Stellmacher.elementaryAbelianMaxJ R).map (MulAut.conj r).toMonoidHom = _
  rw [← Stellmacher.elementaryAbelianMaxJ_map_equiv]
  have hn : R.map (MulAut.conj r).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (R.le_normalizer hr)
  rw [hn]

/-- If the Thompson image has the marked fixed letter, the whole original
actor preserves the lifted six-point stabilizer. -/
theorem normalizes_preimage_of_marking (K H R : Subgroup G)
    (hK : K ≤ H) (hR : R ≤ H) (hRK : R ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (ρ : H →* Perm (Fin 7))
    (hρ : ∀ k : K, ρ ⟨k, hK k.property⟩ = (blockProjection K e k : Perm (Fin 7)))
    (hmark : actionImage H ρ (Stellmacher.elementaryAbelianMaxJ R) = threeTranspositions) :
    R ≤ normalizer (ambientPreimage K e 6 : Set G) := by
  have hfix (r : R) : ρ ⟨r, hR r.property⟩ (6 : Fin 7) = 6 := by
    apply normalizer_threeTranspositions_fix_six
    rw [← hmark]
    exact actionImage_normalizer H _ ρ
      ((show Stellmacher.elementaryAbelianMaxJ R ≤ R from
        sSup_le fun _ hA => hA.1).trans hR)
      ⟨r, hR r.property⟩ (normalizes_thompson R r.property)
  have hclosed (r : R) (b : G) (hb : b ∈ ambientPreimage K e 6) :
      (r : G) * b * (r : G)⁻¹ ∈ ambientPreimage K e 6 := by
    have hbK : b ∈ K := map_subtype_le _ hb
    have hcK : (r : G) * b * (r : G)⁻¹ ∈ K :=
      (mem_normalizer_iff.mp (hRK r.property) b).mp hbK
    apply (mem_ambientPreimage K e 6 ⟨_, hcK⟩).mpr
    rw [← hρ]
    have he : (⟨(r : G) * b * (r : G)⁻¹, hK hcK⟩ : H) =
        ⟨r, hR r.property⟩ * ⟨b, hK hbK⟩ * ⟨r, hR r.property⟩⁻¹ := rfl
    rw [he, map_mul, map_mul, map_inv]
    change (ρ ⟨r, hR r.property⟩)
      ((ρ ⟨b, hK hbK⟩) ((ρ ⟨r, hR r.property⟩)⁻¹ 6)) = 6
    have hinv : (ρ ⟨r, hR r.property⟩)⁻¹ (6 : Fin 7) = 6 := by
      apply (ρ ⟨r, hR r.property⟩).injective
      simpa using (hfix r).symm
    rw [hinv, hρ ⟨b, hbK⟩, (mem_ambientPreimage K e 6 ⟨b, hbK⟩).mp hb, hfix]
  intro r hr
  rw [mem_normalizer_iff]
  intro b
  constructor
  · exact hclosed ⟨r, hr⟩ b
  · intro hb
    have hh := hclosed (⟨r, hr⟩ : R)⁻¹ _ hb
    simpa [mul_assoc] using hh

variable [Finite G]

/-- The ambient core of the constructed lift is killed by the original
K/O₂(K) map, using the already proved kernel of the residual-lift projection. -/
theorem replacement_core_projection (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) (x : Fin 7)
    (b : G) (hb : b ∈ (replacement K e x).pCoreIn 2) :
    blockProjection K e ⟨b, replacement_le K e x (pCoreIn_le 2 _ hb)⟩ = 1 := by
  obtain ⟨c, hc, rfl⟩ := hb
  let R := residualLift (blockProjection K e) x
  let a : R ≃* replacement K e x := R.equivMapOfInjective K.subtype K.subtype_injective
  have hd : a.symm c ∈ pCore 2 R := by
    rw [← pCore_map_iso 2 a] at hc
    obtain ⟨d, hd, he⟩ := hc
    rw [← he]
    change a.symm (a d) ∈ pCore 2 R
    rw [MulEquiv.symm_apply_apply]
    exact hd
  have hk := liftProjection_kernel_eq_core (blockProjection K e)
    (blockProjection_surjective K e)
    (by rw [blockProjection_kernel]; exact pCore_isPGroup) x
  have hz : liftProjection (blockProjection K e) x (a.symm c) = 1 := by
    change a.symm c ∈ (liftProjection (blockProjection K e) x).ker
    rw [hk]
    exact hd
  have he : (((a.symm c : R) : K) : G) = (c : G) := by
    exact congrArg Subtype.val (a.apply_symm_apply c)
  have he' : ((a.symm c : R) : K) =
      ⟨(c : G), replacement_le K e x c.property⟩ :=
    Subtype.ext he
  have hz' := congrArg Subtype.val hz
  change blockProjection K e ((a.symm c : R) : K) = 1 at hz'
  rwa [he'] at hz'

private def actorCycle : alternatingGroup (Fin 7) :=
  ⟨swap 0 1 * swap 0 2,
    (isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)).mem_alternatingGroup⟩

private theorem actorCycle_mem : actorCycle ∈ sixStabilizer 6 := by
  rw [mem_sixStabilizer_iff]
  decide

private theorem actorCycle_noncommuting :
    ⁅swap (0 : Fin 7) 1, (actorCycle : Perm (Fin 7))⁆ ≠ 1 := by
  decide

/-- Lift the concrete transposition/three-cycle actor through the existing
residual lift. The conclusion is the literal witness needed for Y_z selection. -/
theorem exists_actor_of_marking (K H R : Subgroup G)
    (hK : K ≤ H)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (ρ : H →* Perm (Fin 7))
    (hρ : ∀ k : K, ρ ⟨k, hK k.property⟩ = (blockProjection K e k : Perm (Fin 7)))
    (hmark : actionImage H ρ (Stellmacher.elementaryAbelianMaxJ R) = threeTranspositions) :
    ∃ j ∈ Stellmacher.elementaryAbelianMaxJ R, ∃ b ∈ replacement K e 6,
      ⁅j, b⁆ ∉ (replacement K e 6).pCoreIn 2 := by
  have hj : swap (0 : Fin 7) 1 ∈ actionImage H ρ (Stellmacher.elementaryAbelianMaxJ R) := by
    rw [hmark]
    exact subset_closure (by simp)
  obtain ⟨j, hj, hjρ⟩ := hj
  have hb : actorCycle ∈ (residualLift (blockProjection K e) 6).map (blockProjection K e) := by
    rw [residualLift_image _ (blockProjection_surjective K e)]
    exact actorCycle_mem
  obtain ⟨b, hb, hbρ⟩ := hb
  have hbB : (b : G) ∈ replacement K e 6 := ⟨b, hb, rfl⟩
  refine ⟨j, hj, b, hbB, ?_⟩
  intro hc
  have hcK : ⁅(j : G), (b : G)⁆ ∈ K := replacement_le K e 6 (pCoreIn_le 2 _ hc)
  have hz := replacement_core_projection K e 6 _ hc
  have he : (⟨⁅(j : G), (b : G)⁆, hK hcK⟩ : H) = ⁅j, ⟨b, hK b.property⟩⁆ := rfl
  have hzρ : ρ ⟨⁅(j : G), (b : G)⁆, hK hcK⟩ = 1 := by
    rw [hρ ⟨_, hcK⟩, hz]
    rfl
  rw [he, map_commutatorElement, hjρ, hρ, hbρ] at hzρ
  exact actorCycle_noncommuting hzρ

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.OrdinarySeven.SourcePlacement
end
