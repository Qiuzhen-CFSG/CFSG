module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneEscape

/-!
# First-edge normality and paired generation in the cubic plane branch

For every small critical pair, the first-edge group normalizes the full
critical seed kernel. The plane image is abelian, so it normalizes the
critical commutator; the exact kernel/line normalizer identity then gives
normality of the original kernel, including its central attachment.

Generation must still use both endpoints of the paired selector. A plane
radical and a single transposition preserve a proper duad: one of the three
pairs is disjoint from the transposition. They cannot generate S₆. Faithful
edge charts and the actual projection lift this obstruction to every
neighbor of every original small critical path. In particular no choice
of a single edge gives Q_t join Z_z = G_a in this branch. The kernel of the
projection is still E, not Q; no claim that the radical is Sylow is used.

These are the first-edge normality and generation distinctions needed for
MS93 (5.12)(3). The single-endpoint generation invoked on p.926 belongs to
the other Thompson branch. The plane branch requires the simultaneous
paired generation at the shifted vertex on p.927. Neither that generation
nor the two end-slice bounds follows here. The whole-core and literal
C.1.32 applications preserve both full covers and the Borel alternative;
both core exhaustions and final reconstruction remain open.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.6) and (5.12)(3), printed pp.917--918,926--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped Pointwise
namespace PlaneSingleGeneration
private theorem fixed_pair_certificate : ∀ i j : Fin 6, ∃ d : Duad,
    (duadSet d).image swap01 = duadSet d ∧
    (duadSet d).image swap23 = duadSet d ∧
    (duadSet d).image swap45 = duadSet d ∧
    (duadSet d).image (Equiv.swap i j) = duadSet d := by decide
private theorem moved_pair_certificate : ∀ d : Duad, ∃ i j : Fin 6,
    (duadSet d).image (Equiv.swap i j) ≠ duadSet d := by decide

private theorem plane_swap_ne_top (a : S) (ha : a.IsSwap) : D ⊔ zpowers a ≠ ⊤ := by
  obtain ⟨i,j,_,rfl⟩ := ha
  obtain ⟨d,h01,h23,h45,hs⟩ := fixed_pair_certificate i j
  let H := MulAction.stabilizer S d
  have mem (g : S) (hg : (duadSet d).image g = duadSet d) : g ∈ H := by
    apply duadSet_injective
    exact (duadSet_smul g d).trans hg
  have hD : D ≤ H := by
    rw [D,closure_le]
    rintro g (rfl | rfl | rfl)
    · exact mem _ h01
    · exact mem _ h23
    · exact mem _ h45
  have hle : D ⊔ zpowers (Equiv.swap i j) ≤ H := sup_le hD (zpowers_le.mpr (mem _ hs))
  intro he
  obtain ⟨k,l,hn⟩ := moved_pair_certificate d
  have hm : Equiv.swap k l ∈ H := (he ▸ hle) (mem_top _)
  apply hn
  exact (duadSet_smul _ _).symm.trans (congrArg duadSet hm)

private theorem conjugate_plane_swap_ne_top (u a : S) (ha : a.IsSwap) :
    D.map (MulAut.conj u).toMonoidHom ⊔ zpowers a ≠ ⊤ := by
  let b := (MulAut.conj u⁻¹) a
  have hb : b.IsSwap := by
    obtain ⟨i,j,hij,rfl⟩ := ha
    change (u⁻¹ * Equiv.swap i j * (u⁻¹)⁻¹).IsSwap
    rw [←Equiv.swap_apply_apply]
    exact ⟨_,_,u.symm.injective.ne hij,rfl⟩
  intro he
  apply plane_swap_ne_top b hb
  have hm := congrArg (Subgroup.map (MulAut.conj u⁻¹).toMonoidHom) he
  have hback : (D.map (MulAut.conj u).toMonoidHom).map
      (MulAut.conj u⁻¹).toMonoidHom = D := by
    rw [map_map,show (MulAut.conj u⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
        MonoidHom.id S by
      apply MonoidHom.ext
      intro y
      change u⁻¹*(u*y*u⁻¹)*(u⁻¹)⁻¹=y
      group,Subgroup.map_id]
  rw [Subgroup.map_sup,hback,MonoidHom.map_zpowers,
    map_top_of_surjective _ (MulAut.conj u⁻¹).surjective] at hm
  exact hm
end PlaneSingleGeneration

open Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem plane_small_critical_no_single_generator_base
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    {t : Vertex Rg} (hat : Adjacent Rg (alpha Rg) t) :
    Q Rg t ⊔ Z Rg z ≠ stabilizer Rg (alpha Rg) := by
  obtain ⟨a,ha,hA⟩ := small_critical_image_eq_swap h e hz hk p hsmall
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) (base_adjacent Rg) hat
  have hgmem : g ∈ (embedM Rg).range := by
    change g ∈ Mbar Rg
    rwa [←stabilizer_m_base Rg]
  obtain ⟨m,hm⟩ := hgmem
  change act Rg g (beta Rg) = t at hgt
  let T := (Rg).map (MulAut.conj m⁻¹).toMonoidHom
  let A := (Z Rg z).comap (embedM Rg)
  have hAm : A.map (embedM Rg) = Z Rg z := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  have hTm : T.map (embedM Rg) = Q Rg t := by
    have hf : (embedM Rg).comp (MulAut.conj m⁻¹).toMonoidHom =
        (MulAut.conj g⁻¹).toMonoidHom.comp (embedM Rg) := by
      apply MonoidHom.ext
      intro y
      change embedM Rg (m⁻¹*y*(m⁻¹)⁻¹) = g⁻¹*embedM Rg y*(g⁻¹)⁻¹
      simp only [map_mul,map_inv,hm]
    rw [show T = (Rg).map (MulAut.conj m⁻¹).toMonoidHom from rfl,map_map,hf,←map_map,
      ←Q_beta,←Q_act,hgt]
  have hTim : T.map π = D.map (MulAut.conj ((π m)⁻¹*u)).toMonoidHom := by
    have hf : (π).comp (MulAut.conj m⁻¹).toMonoidHom =
        (MulAut.conj (π m)⁻¹).toMonoidHom.comp π := by
      apply MonoidHom.ext
      intro y
      change π (m⁻¹*y*(m⁻¹)⁻¹) = (π m)⁻¹*π y*((π m)⁻¹)⁻¹
      simp only [map_mul,map_inv]
    have hc : (MulAut.conj (π m)⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
        (MulAut.conj ((π m)⁻¹*u)).toMonoidHom := by
      apply MonoidHom.ext
      intro y
      change (π m)⁻¹*(u*y*u⁻¹)*((π m)⁻¹)⁻¹ =
        ((π m)⁻¹*u)*y*((π m)⁻¹*u)⁻¹
      group
    rw [show T = (Rg).map (MulAut.conj m⁻¹).toMonoidHom from rfl,map_map,hf,←map_map,
      hR,map_map,hc]
  intro hgen
  have htop : T ⊔ A = ⊤ := by
    apply map_injective (embedM_injective Rg)
    rw [Subgroup.map_sup,hTm,hAm,hgen,←MonoidHom.range_eq_map]
    exact stabilizer_m_base Rg
  have hh := congrArg (Subgroup.map π) htop
  rw [Subgroup.map_sup,hTim,hA,map_top_of_surjective _
    (CubicEven.projection_surjective h e hz hk)] at hh
  exact PlaneSingleGeneration.conjugate_plane_swap_ne_top _ a ha hh

include h e hz hk in
/-- No single neighboring edge and small critical endpoint generate the
starting stabilizer in the original plane branch, at any vertex. -/
theorem plane_small_critical_no_single_generator
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4)
    {t : Vertex Rg} (hat : Adjacent Rg a t) :
    Q Rg t ⊔ Z Rg z ≠ stabilizer Rg a := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hga : act Rg g (alpha Rg) = a := by
    rw [hg]
    simp only [alpha,act_mVertex,one_mul]
  have hback : act Rg g⁻¹ a = alpha Rg := by
    rw [←hga,←act_mul,mul_inv_cancel,act_one]
  have hp : Nonempty (CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg g⁻¹ z)) := by
    rw [←hback]
    exact ⟨p.act g⁻¹⟩
  obtain ⟨q⟩ := hp
  have hs : (Q Rg (act Rg g⁻¹ z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hback,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hsmall
  have ht : Adjacent Rg (alpha Rg) (act Rg g⁻¹ t) := by
    rw [←hback]
    exact (adjacent_act_iff Rg g⁻¹ _ _).mpr hat
  intro hgen
  apply plane_small_critical_no_single_generator_base h e hz hk u hR q hs ht
  have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹⁻¹).toMonoidHom) hgen
  rw [Subgroup.map_sup,←Q_act Rg g⁻¹,←Z_act Rg g⁻¹,
    ←stabilizer_act Rg g⁻¹,hback] at hh
  exact hh

include h e hz hk in
/-- The actual full critical kernel is normalized by its first-edge group.
This is relative normality in the original graph, with no slice bound. -/
theorem plane_small_critical_first_edge_normalizes_kernel
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hsmall : (Q Rg z).relIndex (Z Rg a) < 4) :
    Q Rg (p.walk.getVert 1) ≤
      normalizer (Z Rg a ⊓ Q Rg z : Set (FreeAmalgam Rg)) := by
  have hab : ⁅(Rg).map π,(Rg).map π⁆ = ⊥ := by
    rw [hR,←map_commutator]
    let := Theory.SpecificGroups.SymmetricSix.BinaryFlags.D_elementary
    rw [commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr inferInstance),Subgroup.map_bot]
  have hn := critical_commutator_normalized_first_of_abelian_image h e hz hk hab p
  have hat : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  have hG : Q Rg (p.walk.getVert 1) ≤ stabilizer Rg a :=
    fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  exact ((le_inf hG hn).trans_eq
    (small_critical_kernel_normalizer_eq_line_normalizer h e hz hk p hsmall).symm).trans
      inf_le_right

omit hk in
include h e hz in
/-- Whole-core application retaining the first-edge kernel normality and
the necessity of paired endpoints in the remaining plane branch. -/
theorem coreExhaustion_or_cubic_plane_source_generation :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
          (Q Rg z).relIndex (Z Rg a) < 4 →
          Q Rg (p.walk.getVert 1) ≤
              normalizer (Z Rg a ⊓ Q Rg z : Set (FreeAmalgam Rg)) ∧
          ∀ t, Adjacent Rg a t → Q Rg t ⊔ Z Rg z ≠ stabilizer Rg a)) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,?_⟩⟩
    intro a z p hp
    exact ⟨plane_small_critical_first_edge_normalizes_kernel h e hz hk u hplane p hp,
      fun _ ht => plane_small_critical_no_single_generator h e hz hk u hplane p hp ht⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the original plane source-generation
obstruction, preserving the full cubic kernel and both moving covers. -/
theorem rankTwo_or_cubic_plane_source_generation :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
          (Q Rg z).relIndex (Z Rg a) < 4 →
          Q Rg (p.walk.getVert 1) ≤
              normalizer (Z Rg a ⊓ Q Rg z : Set (FreeAmalgam Rg)) ∧
          ∀ t, Adjacent Rg a t → Q Rg t ⊔ Z Rg z ≠ stabilizer Rg a)) :=
  (coreExhaustion_or_cubic_plane_source_generation h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
