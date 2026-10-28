module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.LinearThree
public import Theory.GroupTheory.PerfectNormalizerLift

/-!
# The actual special-linear FF actor with a local A₅ section

The central projection SL₃ → PSL₃ has a two-group restricted kernel on
the smaller component: its image in the centerless A₅ core quotient is
trivial. The projective placement theorem therefore applies to the original
marking. Perfectness reflects containment through the central kernel and
lifts the conjugate point or line residual back to SL₃ itself.
Order 168 excludes the binary endpoint, so no lower bound on the binary
field exponent remains in the complete placement and image consumers.

Source: Aschbacher–Smith 10.2.9, pp.751–752, the actual linear-natural
actor in B.4.2/B.5.1.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3 Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
noncomputable section
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] [Finite F] in
private theorem projection_restricted_kernel_two (B : Subgroup SL(3,F))
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    IsPGroup 2 ((projection F).subgroupMap B).ker := by
  let f := (projection F).subgroupMap B
  have hle : f.ker ≤ pCore 2 B := by
    intro b hb
    have hc : (b : SL(3,F)) ∈ center SL(3,F) := by
      rw [← projection_ker]
      exact congrArg Subtype.val hb
    have hbcenter : b ∈ center B := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (mem_center_iff.mp hc y)
    let q := QuotientGroup.mk' (pCore 2 B)
    have hz : e (q b) ∈ center (alternatingGroup (Fin 5)) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z,rfl⟩ := e.surjective y
      obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) z
      rw [← e.map_mul,← e.map_mul,← q.map_mul,← q.map_mul,
        mem_center_iff.mp hbcenter z]
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hz
    exact (QuotientGroup.eq_one_iff b).mp (e.injective (hz.trans e.map_one.symm))
  exact pCore_isPGroup.to_le hle

theorem special_linear_three_five_section_placement {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (S : Sylow 2 SL(3,F)) (B : Subgroup SL(3,F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    Nat.card F = 4 ∧ ∃ g : SL(3,F),
      B.map (MulAut.conj g).toMonoidHom = pointLocalSL F ∨
      B.map (MulAut.conj g).toMonoidHom = lineLocalSL F := by
  let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
  let : Group.IsPerfect B := by
    let := hB.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup SL(3,F)) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  have hker : (projection F).ker ≤ center SL(3,F) := (projection_ker F).le
  have hp : B.map (projection F) ≠ ⊤ := by
    intro ht
    apply hproper
    apply top_unique
    apply le_of_map_le_of_perfect (projection F) hker ⊤ B
    rw [ht]
    exact le_top
  obtain ⟨hfour,g,hg⟩ := linear_three_five_section_image hF hn
    (projection F) (projection_surjective F) inferInstance S B hB
    (projection_restricted_kernel_two B e) hp e
  obtain ⟨g,rfl⟩ := projection_surjective F g
  let A := B.map (MulAut.conj g).toMonoidHom
  let := Group.IsPerfect.map (MulAut.conj g).toMonoidHom (H := B)
  have he : A.map (projection F) = (B.map (projection F)).map
      (MulAut.conj (projection F g)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
  refine ⟨hfour,g,?_⟩
  rcases hg with hg | hg
  · left
    let := pointLocalSL_isPerfect F (by omega)
    have hh : A.map (projection F) = (pointLocalSL F).map (projection F) := he.trans hg
    exact le_antisymm (le_of_map_le_of_perfect (projection F) hker A _ hh.le)
      (le_of_map_le_of_perfect (projection F) hker _ A hh.ge)
  · right
    let := lineLocalSL_isPerfect F (by omega)
    have hh : A.map (projection F) = (lineLocalSL F).map (projection F) := he.trans hg
    exact le_antisymm (le_of_map_le_of_perfect (projection F) hker A _ hh.le)
      (le_of_map_le_of_perfect (projection F) hker _ A hh.ge)
omit [CharP F 2] in
private theorem linear_three_degree_gt_one {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (B : Subgroup SL(3,F)) (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    1 < n := by
  have hcard := Finite.one_lt_card (α := F)
  by_contra! hn
  have hn1 : n = 1 := by
    by_cases hz : n = 0
    · simp [hz] at hF
      omega
    · omega
  have htwo : Nat.card F = 2 := by simpa [hn1] using hF
  let A := B.map (projection F)
  let f := (projection F).subgroupMap B
  let ea : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5) :=
    (f.quotientPCoreEquivOfSurjective ((projection F).subgroupMap_surjective B)
      (projection_restricted_kernel_two B e)).symm.trans e
  have hd : 60 ∣ Nat.card PSL(3,F) := by
    have h := (card_quotient_dvd_card (pCore 2 A)).trans A.card_subgroup_dvd_card
    rw [Nat.card_congr ea.toEquiv, nat_card_alternatingGroup] at h
    norm_num [Nat.factorial] at h ⊢
    exact h
  rw [Matrix.PSL3.LinearThree.card_projective F,htwo] at hd
  norm_num at hd

theorem special_linear_three_five_section_placement_all {n : ℕ}
    (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 SL(3,F)) (B : Subgroup SL(3,F))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    Nat.card F = 4 ∧ ∃ g : SL(3,F),
      B.map (MulAut.conj g).toMonoidHom = pointLocalSL F ∨
      B.map (MulAut.conj g).toMonoidHom = lineLocalSL F :=
  special_linear_three_five_section_placement hF (linear_three_degree_gt_one hF B e)
    S B hB hproper e

theorem special_linear_three_five_section_image
    {G : Type*} [Group G] [Finite G] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (f : G →* SL(3,F)) (hf : Function.Surjective f)
    (hks : Group.IsSolvable f.ker) (S : Sylow 2 G) (L : Subgroup G)
    (hL : L ∈ localCComponents S) (hk : IsPGroup 2 (f.subgroupMap L).ker)
    (hproper : L.map f ≠ ⊤)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    Nat.card F = 4 ∧ ∃ g : SL(3,F),
      (L.map f).map (MulAut.conj g).toMonoidHom = pointLocalSL F ∨
      (L.map f).map (MulAut.conj g).toMonoidHom = lineLocalSL F := by
  let := hks
  exact special_linear_three_five_section_placement_all hF
    (S.mapSurjective hf) (L.map f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hL f) hproper
    (((f.subgroupMap L).quotientPCoreEquivOfSurjective
      (f.subgroupMap_surjective L) hk).symm.trans e)
end
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF
