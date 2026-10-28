module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Noncommuting.RootCoreAction

/-!
# The critical fixed line and the other neighbor center

For a natural center with trivial central kernel, every nontrivial
two-subgroup has equal fixed and commutator subgroups. At a critical pair
this is the beta-center. The complementary neighbor center consequently
has trivial intersection with the opposite vertex core. The literal core
and conjugation section are retained throughout.

Source: DGS, *Groups and Graphs* (1985), (7.5)(1), printed p.129,
and the final commutator calculation on p.131.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {G : Type*} [Group G]

private theorem natural_fixed_eq_commutator
    {k : Type*} [Field k] [Finite k] [Algebra (ZMod 2) k]
    (L Z A : Subgroup G) (π : L →* SL(2,k))
    (d : BinaryConjugationSection L Z ⊥
      (SL2NaturalOffenders.NoStrong.natural.comp π))
    (hAL : A ≤ L) (hp : IsPGroup 2 A)
    (hne : (A.subgroupOf L).map π ≠ ⊥) :
    Z ⊓ centralizer (A : Set G) = ⁅Z,A⁆ := by
  let N := SL2NaturalOffenders.NoStrong.natural (F := k)
  obtain ⟨T,hT⟩ := (hp.comap_subtype.map π).exists_le_sylow
  have he : commutatorPreimage Z A ⊥ = Z ⊓ centralizer (A : Set G) := by
    apply le_antisymm
    · exact le_inf (commutatorPreimage_le _ _ _)
        (commutator_eq_bot_iff_le_centralizer.mp
          (bot_unique (commutator_commutatorPreimage_le Z A ⊥ le_normalizer_of_normal)))
    · exact le_commutatorPreimage inf_le_left
        (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le
  have hfixed : d.imageSpace (Z ⊓ centralizer (A : Set G)) =
      fixedSpace N ((A.subgroupOf L).map π) := by
    rw [←fixedSpace_comp_map,←d.fixed_image_eq A hAL le_normalizer_of_normal,he]
  have hmove : d.imageSpace ⁅Z,A⁆ = fixedSpace N ((A.subgroupOf L).map π) := by
    rw [commutator_comm Z A,d.imageSpace_commutator A Z hAL le_rfl,
      d.imageSpace_self,subspaceCommutator_comp_map]
    exact (natural_subgroup_fixed_moved T _ hT hne).2.trans
      (natural_subgroup_fixed_moved T _ hT hne).1.symm
  have hAZ : ⁅Z,A⁆ ≤ Z := le_normalizer_iff_commutator_le_left.mp (hAL.trans d.normalized)
  apply le_antisymm
  · intro z hz
    apply (d.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le ⟨z,hz.1⟩).mp
    rw [hmove,←hfixed]
    exact (d.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le _).mpr hz
  · intro z hz
    apply (d.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le ⟨z,hAZ hz⟩).mp
    rw [hfixed,←hmove]
    exact (d.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le _).mpr hz

theorem natural_center_fixed_eq_commutator
    (L Z Q A : Subgroup G) (hnat : HasNaturalCenter L Z Q)
    (hcenter : center L = ⊥) (hAL : A ≤ L) (hp : IsPGroup 2 A)
    (hAQ : ¬ A ≤ Q) : Z ⊓ centralizer (A : Set G) = ⁅Z,A⁆ := by
  obtain ⟨k,_,_,_,π,_,hk,⟨d⟩⟩ := hnat
  have hω : Stellmacher.omegaOneCenterAmbient L = ⊥ := by
    apply bot_unique
    intro x hx
    obtain ⟨hxL,_,hxc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx
    have hm : (⟨x,hxL⟩ : L) ∈ center L :=
      mem_center_iff.mpr (fun l => Subtype.ext (hxc l l.property))
    rw [hcenter,mem_bot] at hm
    exact congrArg Subtype.val hm
  let d₀ : BinaryConjugationSection L Z ⊥
      (SL2NaturalOffenders.NoStrong.natural.comp π) := hω ▸ d
  apply natural_fixed_eq_commutator L Z A π d₀ hAL hp
  intro hh
  have hh' := (Subgroup.map_eq_bot_iff _).mp hh
  rw [hk] at hh'
  exact hAQ (fun a ha => hh' (show (⟨a,hAL ha⟩ : L) ∈ A.subgroupOf L from ha))

theorem graph_epsilonTwo_other_center_disjoint_core
    {P : Fin 2 → Subgroup G} {B : Subgroup G}
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (L : Vertex (family P) → Subgroup G)
    (d : ∀ x y, (graph (family P)).Adj x y →
      LocalRankOneData (stabilizer (family P) x)
        (stabilizer (family P) x ⊓ stabilizer (family P) y))
    (hstar : ∀ x y he, (d x y he).Pstar = L x)
    (hodd : ∀ x, ¬ 2 ∣ (L x).relIndex (stabilizer (family P) x))
    (hdich : ∀ x, Stellmacher.IsSylowSubgroupIn (Q (family P) x)
      (L x ⊓ centralizer (Z (family P) x : Set G)) ∨
      Z (family P) x = Stellmacher.omegaOneCenterAmbient (L x))
    {v w u a : Vertex (family P)} (hc : IsCriticalPair (family P) v w)
    (hne : ⁅Z (family P) v,Z (family P) w⁆ ≠ ⊥)
    (hvu : (graph (family P)).Adj v u) (hva : (graph (family P)).Adj v a) (hua : u ≠ a)
    (hepsilon : Z (family P) u = Stellmacher.omegaOneCenterAmbient
      ((stabilizer (family P) v ⊓ stabilizer (family P) u).pCoreIn 2))
    (hnat : HasNaturalCenter (L v) (Z (family P) v) (Q (family P) v))
    (hR : ⁅Z (family P) v,Z (family P) w⁆ = Z (family P) u) :
    Z (family P) a ⊓ Q (family P) w = ⊥ := by
  have hcenter : center (L v) = ⊥ := by
    rw [←hstar v u hvu]
    exact graph_epsilonTwo_center_trivial_of_localData h hB hvu (d v u hvu) (d u v hvu.symm)
      (by rw [hstar]; exact hodd v) (by rw [hstar]; exact hodd u)
      (by rw [hstar]; exact hdich u) hepsilon
  let := graph_Z_elementary h w
  have hZWv : Z (family P) w ≤ L v := by
    rw [←hstar v u hvu]
    exact local_twoGroup_le_star (d v u hvu) (by rw [hstar]; exact hodd v)
      _ (IsElementaryAbelian.isPGroup 2 _)
      (Z_le_stabilizer_of_dist_le_b (family P) h.generate w v
        (by rw [SimpleGraph.dist_comm,hc.1]))
  have hAQ : ¬ Z (family P) w ≤ Q (family P) v := by
    intro hh
    exact hne (commutator_comm _ _ |>.trans
      (commutator_eq_bot_iff_le_centralizer.mpr (hh.trans (graph_Q_centralizes_Z h v))))
  have hf := natural_center_fixed_eq_commutator (L v) (Z (family P) v)
    (Q (family P) v) (Z (family P) w) hnat hcenter hZWv
    (IsElementaryAbelian.isPGroup 2 _) hAQ
  rw [hR] at hf
  have hsplit := graph_epsilonTwo_centers_split_of_type h hB L d hstar hodd hdich
    hvu hepsilon hnat rfl hvu hva hua
  apply bot_unique
  rw [←disjoint_iff.mp hsplit.2]
  apply le_inf
  · exact (le_inf (inf_le_left.trans (hsplit.1 ▸ le_sup_right))
      (inf_le_right.trans (graph_Q_centralizes_Z h w))).trans hf.le
  · exact inf_le_left

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
