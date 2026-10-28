module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardClosure
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.NoncentralSeedChoice
/-!
# The forward commutator line lies in the starting fixed core

When the forward moving layer has Baumann index at most two and the critical
distance is greater than four, its hyperplane-kernel commutator centralizes
the starting component. If a line element did not, the native splitting of
the starting seed would produce a single conjugate with both the required
stabilizer generation and noncentrality. The forward closure contradiction
rules this out.

This is the first half of Meierfrankenfeld--Stellmacher (1993), (5.9), printed
p.920. The literal characteristic replacement below supplies all model data;
the remaining exclusion of the index-two case is a separate argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise

private theorem centralizer_line_eq_singleton {G : Type*} [Group G]
    (H : Subgroup G) [Finite H] (hcard : Nat.card H ≤ 2)
    {z : G} (hz : z ∈ H) (hzn : z ≠ 1) :
    centralizer (H : Set G) = centralizer ({z} : Set G) := by
  have hne : H ≠ ⊥ := by intro he; exact hzn (mem_bot.mp (he ▸ hz))
  have hpos := (one_lt_card_iff_ne_bot H).mpr hne
  obtain ⟨w,hw,huniq⟩ := (Nat.card_eq_two_iff' (1:H)).mp (by omega)
  have hz' : (⟨z,hz⟩:H) ≠ 1 := fun he => hzn (congrArg Subtype.val he)
  apply le_antisymm (centralizer_le (Set.singleton_subset_iff.mpr hz))
  intro x hx y hy
  by_cases he : y=1
  · simp [he]
  · have hy' : (⟨y,hy⟩:H) ≠ 1 := fun hh => he (congrArg Subtype.val hh)
    have heq : y=z := congrArg Subtype.val ((huniq _ hy').trans (huniq _ hz').symm)
    exact heq ▸ hx z (Set.mem_singleton _)

open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

theorem critical_forward_commutator_le_fixedCore
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 4 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (hindex : (B R (alpha R) (s.geometry.Z_normal _)).relIndex
      (U R (p.walk.getVert 2)) ≤ 2) :
    let T₀ := Q R (alpha R) ⊓ centralizer
      (U R (p.walk.getVert 2) ⊓ B R (alpha R) (s.geometry.Z_normal _) : Set (FreeAmalgam R))
    ⁅U R (p.walk.getVert 2),T₀⁆ ≤ fixedCore R (alpha R) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T₀ := Q R (alpha R) ⊓ centralizer
    (U R c ⊓ B R (alpha R) (s.geometry.Z_normal _) : Set (FreeAmalgam R))
  let H := ⁅U R c,T₀⁆
  change H ≤ fixedCore R (alpha R)
  have hb2 : 2 < s.geometry.b R := by omega
  have hl := p.length_eq_b
  have hc : color R c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R (alpha R) t := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i:=0) (by omega)
  have hct : Adjacent R c t := adjacent_symm R ((cosetGraph_adj R _ _).mp
    (p.walk.adj_getVert_succ (i:=1) (by omega)))
  have hV : U R c ≤ V R (alpha R) := (DistanceEight.U_le_Z R c).trans
    (le_iSup_of_le c (le_iSup_of_le (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)]) le_rfl))
  have hB : ¬ U R c ≤ B R (alpha R) (s.geometry.Z_normal _) := by
    intro he
    have hn := s.forward_moving_index_two_le h u hfull hb2 p
    have hh := relIndex_eq_one.mpr he
    change (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R c) = 1 at hh
    change 2 ≤ (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R c) at hn
    omega
  obtain ⟨hcard,hseed⟩ := s.moving_hyperplane_commutator_le_seed h u hfull rfl hc hat hct hindex
  have hHZ : H ≤ Z R (alpha R) := hseed.trans (adjacent_Z_le R rfl hat)
  have hTN : stabilizer R (alpha R) ≤ normalizer (T₀ : Set (FreeAmalgam R)) :=
    s.moving_hyperplane_kernel_normalized hb2 rfl hat hct
  intro z hz
  by_contra hzn
  obtain ⟨g,hg,hgen,hgne⟩ := s.exists_noncentral_seed_generator h u hfull p (hHZ hz) hzn
  have hgG := Ltilde_le_stabilizer (alpha R) hg
  let f := (MulAut.conj g).toMonoidHom
  let A := (U R c).map f
  let H₁ := H.map f
  have hVm : (V R (alpha R)).map f = V R (alpha R) :=
    mem_normalizer_iff_map_conj_eq.mp ((DistanceEight.V_normalized R (alpha R)) hgG)
  have hBm : (B R (alpha R) (s.geometry.Z_normal _)).map f = B R (alpha R) (s.geometry.Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb2 (alpha R) rfl hgG)
  have hTm : T₀.map f = T₀ := mem_normalizer_iff_map_conj_eq.mp (hTN hgG)
  have hZm : (Z R (alpha R)).map f = Z R (alpha R) :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized R (alpha R) hgG)
  have hAZ : A ≤ V R (alpha R) := hVm ▸ map_mono hV
  have hAB : ¬ A ≤ B R (alpha R) (s.geometry.Z_normal _) := by
    intro he
    apply hB
    apply (map_le_map_iff_of_injective (f:=f) (MulAut.conj g).injective).mp
    rwa [hBm]
  have hH₁Z : H₁ ≤ Z R (alpha R) := hZm ▸ map_mono hHZ
  have hcard₁ : Nat.card H₁ ≤ 2 := by
    rw [show Nat.card H₁ = Nat.card H from card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  let := finite_Z R (alpha R)
  let : Finite H₁ := Finite.of_injective (inclusion hH₁Z) (inclusion_injective _)
  have hz₁ : g*z*g⁻¹ ∈ H₁ := mem_map_of_mem f hz
  have hz₁n : g*z*g⁻¹ ≠ 1 := fun he => hgne (he ▸ (centralizer (Z R e : Set (FreeAmalgam R))).one_mem)
  have hC := centralizer_line_eq_singleton H₁ hcard₁ hz₁ hz₁n
  have hgen₁ : (stabilizer R (alpha R) ⊓ centralizer (H₁ : Set (FreeAmalgam R))) ⊔
      Z R e = stabilizer R (alpha R) := by rw [hC]; exact hgen
  have hcomm : ⁅A,T₀⁆ ≤ H₁ := by
    change ⁅(U R c).map f,T₀⁆ ≤ H.map f
    rw [show H = ⁅U R c,T₀⁆ from rfl,map_commutator,hTm]
  exact s.critical_controlled_line_false h u hfull hb p A T₀ H₁ hAZ hAB inf_le_left hTN
    hH₁Z hcard₁ (fun he => hgne (he hz₁)) hgen₁ hcomm
    (s.critical_forward_kernel_contains_inner_layers hb p)
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

theorem reducedSource_block_or_forward_fixed_line
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : 4 < ((originalSource d hm).reduce r).geometry.b r.radical)
    (hindex : (B r.radical (alpha r.radical) (((originalSource d hm).reduce r).geometry.Z_normal _)).relIndex
      (U r.radical (p.walk.getVert 2)) ≤ 2) :
    IsAlternatingBlock L 6 ∨
      (let T₀ := Q r.radical (alpha r.radical) ⊓ centralizer
         (U r.radical (p.walk.getVert 2) ⊓ B r.radical (alpha r.radical)
           (((originalSource d hm).reduce r).geometry.Z_normal _) : Set (FreeAmalgam r.radical))
       ⁅U r.radical (p.walk.getVert 2),T₀⁆ ≤ fixedCore r.radical (alpha r.radical)) := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock | hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have h := reduced_nativeCentralLayer d hm r
    have hf : r.radical.map s.projection = Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.critical_forward_commutator_le_fixedCore h _ hf hb p hindex
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
