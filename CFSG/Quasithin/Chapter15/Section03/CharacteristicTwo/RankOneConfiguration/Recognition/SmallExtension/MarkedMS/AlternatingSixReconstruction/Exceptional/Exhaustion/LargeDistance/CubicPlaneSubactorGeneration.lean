module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSourceGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSelectors
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRemainingRadicals
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePlane
public import Theory.SpecificGroups.SymmetricSix.Parabolics.QuadrangleActions

/-!
# Large subactors in the original generating plane pairs

For two plane radicals generating S₆, every subgroup of order greater than
two in one plane still generates S₆ with the other. The fifteen synthemes
reduce the pair to opposite matchings. The seven four-subgroups of the
three-transposition group then give the five adjacent transpositions by
short checked words.

A single faithful edge chart lifts this calculation to every component
vertex of the original cubic graph. Image orders are computed through the
actual projection with kernel E; the no-supplement theorem then lifts
generation across E, retaining its odd quotient E/Q. Applying the result
to the existing normalized selector preserves its component switch, both
generation identities, and its first-edge normalization and containment.
The latter containment also makes the selected edge generate with the
original first edge, giving the literal large-subactor comparison there.

This strengthens the binary full-plane case of MS93 (5.6)(a) to the
large-subactor bound used in (5.12)(3). Constructing that shifted configuration,
proving its normality and the two small-slice bounds, and completing both
core exhaustions remain separate obligations. The whole-core and literal
C.1.32 consumers retain both moving covers and the Borel alternative.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.6)(a) and (5.12)(3), printed pp.917--918,927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/


public noncomputable section
open Subgroup Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterB.Offenders.SixCorePlane (cube_eq opposite)
namespace PlaneSubactor
private def roots (i : Fin 3) : S := ![swap01,swap23,swap45] i
private theorem roots_mem (i : Fin 3) : roots i ∈ D := by
  fin_cases i
  · exact swap01_mem_D
  · exact swap23_mem_D
  · exact swap45_mem_D
private theorem dWords_mem (i : Fin 8) : dWords i ∈ D := by
  rw [cube_eq]
  exact (mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨i,rfl⟩
private theorem mem_D {a : S} (ha : a ∈ D) : ∃ i : Fin 8, dWords i = a := by
  rw [cube_eq] at ha
  exact (mem_disjointTranspositions_iff (3 : Fin 4) _).mp ha
private def duadSwap (d : Duad) : S :=
  ![Equiv.swap 0 1,Equiv.swap 0 2,Equiv.swap 0 3,Equiv.swap 0 4,Equiv.swap 0 5,
    Equiv.swap 1 2,Equiv.swap 1 3,Equiv.swap 1 4,Equiv.swap 1 5,
    Equiv.swap 2 3,Equiv.swap 2 4,Equiv.swap 2 5,
    Equiv.swap 3 4,Equiv.swap 3 5,Equiv.swap 4 5] d
private def baseDuads (j : Fin 3) : Duad := ![0,9,14] j
private theorem duadSwap_pair : ∀ d : Duad, ∀ i j : Fin 6,
    duadSet d = {i,j} → duadSwap d = Equiv.swap i j := by decide
private theorem syntheme_certificate : ∀ s : Syntheme,
    (∃ i : Fin 3, ∀ d ∈ synthemeDuads s,
      roots i * duadSwap d = duadSwap d * roots i) ∨
    (∃ c : Fin 8, ∀ d ∈ synthemeDuads s, ∃ k : Fin 3,
      dWords c * duadSwap d * (dWords c)⁻¹ = opposite * roots k * opposite⁻¹) := by decide

private theorem opposite_certificate (u : S) :
    (∃ i : Fin 3, ∀ j : Fin 3,
      roots i * (u*roots j*u⁻¹) = (u*roots j*u⁻¹) * roots i) ∨
    (∃ c : Fin 8, ∀ j : Fin 3, ∃ k : Fin 3,
      dWords c * (u*roots j*u⁻¹) * (dWords c)⁻¹ =
        opposite * roots k * opposite⁻¹) := by
  have hm (j : Fin 3) : duadSwap (u • baseDuads j) = u*roots j*u⁻¹ := by
    fin_cases j
    all_goals
      rw [show roots _ = Equiv.swap _ _ from rfl,←Equiv.swap_apply_apply]
      apply duadSwap_pair
      rw [duadSet_smul]
      simp [baseDuads,duadSet,duadTable,pair]
  have hin (j : Fin 3) : u • baseDuads j ∈ synthemeDuads (synthemeAct u 0) := by
    rw [synthemeDuads_act]
    exact Finset.mem_image_of_mem _ (by fin_cases j <;> decide)
  rcases syntheme_certificate (synthemeAct u 0) with ⟨i,hi⟩ | ⟨c,hc⟩
  · exact Or.inl ⟨i,fun j => by simpa only [hm j] using hi _ (hin j)⟩
  · exact Or.inr ⟨c,fun j => by simpa only [hm j] using hc _ (hin j)⟩

private def basis (i : Fin 7) : Fin 8 × Fin 8 :=
  ![(1,2),(1,4),(1,6),(2,4),(2,5),(3,4),(3,5)] i
private theorem basis_certificate : ∀ i j : Fin 8,
    dWords i ≠ 1 → dWords j ≠ 1 → dWords j ≠ dWords i →
    ∃ k : Fin 7,
      (dWords (basis k).1 = dWords i ∨ dWords (basis k).1 = dWords j ∨
        dWords (basis k).1 = dWords i*dWords j) ∧
      (dWords (basis k).2 = dWords i ∨ dWords (basis k).2 = dWords j ∨
        dWords (basis k).2 = dWords i*dWords j) := by decide
private def generatingWords (k : Fin 7) (i : Fin 5) : List (Fin 5) :=
  ![![[3], [0,3,0], [4], [1], [1,2,3,0,4,0,1,3,2]],
    ![[3], [0,3,0], [0,1,3,2,4,1,2,3,0], [1], [4]],
    ![[3], [0,3,0], [0,4,0,4,0], [1], [2,4,2,4,2]],
    ![[0,2,3,1,4,1,2,3,0], [2,3,1,4,1,2,3], [3], [1], [4]],
    ![[0,4,0,4,0], [4,0,4], [3], [1], [1,4,1,4,1]],
    ![[2,3,2,3,2], [0,2,3,2,3,0,2], [1,3,1,3,1], [1], [4]],
    ![[0,4,0,4,0], [4,0,4], [1,3,1,3,1], [1], [1,4,1,4,1]]] k i
private def generators (k : Fin 7) (i : Fin 5) : S :=
  ![opposite*swap01*opposite⁻¹,opposite*swap23*opposite⁻¹,
    opposite*swap45*opposite⁻¹,dWords (basis k).1,dWords (basis k).2] i
private theorem generating_certificate : ∀ k : Fin 7, ∀ i : Fin 5,
    ((generatingWords k i).map (generators k)).prod = Equiv.swap i.castSucc i.succ := by
  intro k i
  fin_cases k <;> fin_cases i <;> decide +kernel

private theorem standard_generate (A : Subgroup S) (hA : A ≤ D) (hc : 2 < Nat.card A) :
    D.map (MulAut.conj opposite).toMonoidHom ⊔ A = ⊤ := by
  have hn : ¬ A ≤ ⊥ := by
    intro hh
    have hh' := card_le_of_le hh
    rw [card_bot] at hh'
    omega
  obtain ⟨a,ha,ha1⟩ := SetLike.not_le_iff_exists.mp hn
  have ha1 : a ≠ 1 := by simpa using ha1
  have ha2 : a ^ 2 = 1 := by
    obtain ⟨i,rfl⟩ := mem_D (hA ha)
    exact (show ∀ i : Fin 8, dWords i ^ 2 = 1 by decide) i
  have horder : orderOf a = 2 := orderOf_eq_prime ha2 ha1
  have hn' : ¬ A ≤ zpowers a := by
    intro hh
    have hh' := card_le_of_le hh
    rw [Nat.card_zpowers,horder] at hh'
    omega
  obtain ⟨b,hb,hbnot⟩ := SetLike.not_le_iff_exists.mp hn'
  have hb1 : b ≠ 1 := fun he => hbnot (he ▸ (zpowers a).one_mem)
  have hba : b ≠ a := fun he => hbnot (he ▸ mem_zpowers a)
  obtain ⟨i,rfl⟩ := mem_D (hA ha)
  obtain ⟨j,rfl⟩ := mem_D (hA hb)
  obtain ⟨k,hk₁,hk₂⟩ := basis_certificate i j ha1 hb1 hba
  have hmem₁ : dWords (basis k).1 ∈ A := by
    rcases hk₁ with he | he | he
    · exact he.symm ▸ ha
    · exact he.symm ▸ hb
    · exact he.symm ▸ A.mul_mem ha hb
  have hmem₂ : dWords (basis k).2 ∈ A := by
    rcases hk₂ with he | he | he
    · exact he.symm ▸ ha
    · exact he.symm ▸ hb
    · exact he.symm ▸ A.mul_mem ha hb
  let J := D.map (MulAut.conj opposite).toMonoidHom ⊔ A
  have hg (i : Fin 5) : generators k i ∈ J := by
    fin_cases i
    · exact mem_sup_left (mem_map_of_mem _ swap01_mem_D)
    · exact mem_sup_left (mem_map_of_mem _ swap23_mem_D)
    · exact mem_sup_left (mem_map_of_mem _ swap45_mem_D)
    · exact mem_sup_right hmem₁
    · exact mem_sup_right hmem₂
  have hw (l : List (Fin 5)) : (l.map (generators k)).prod ∈ J := by
    induction l with
    | nil => exact J.one_mem
    | cons i l ih => exact J.mul_mem (hg i) ih
  apply top_unique
  rw [←closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5),closure_le]
  rintro _ ⟨i,rfl⟩
  change Equiv.swap i.castSucc i.succ ∈ J
  rw [←generating_certificate k i]
  exact hw _

private theorem conjugate_plane_coordinates (u : S)
    (hgen : D ⊔ D.map (MulAut.conj u).toMonoidHom = ⊤) :
    ∃ c ∈ D, (D.map (MulAut.conj u).toMonoidHom).map
      (MulAut.conj c).toMonoidHom = D.map (MulAut.conj opposite).toMonoidHom := by
  rcases opposite_certificate u with ⟨i,hi⟩ | ⟨c,hc⟩
  · have hD : D ≤ centralizer ({roots i} : Set S) := by
      let := D_elementary
      have hh := le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative D)
      exact hh.trans (centralizer_le (show ({roots i} : Set S) ⊆ D from
        Set.singleton_subset_iff.mpr (roots_mem i)))
    have hU : D.map (MulAut.conj u).toMonoidHom ≤ centralizer ({roots i} : Set S) := by
      rw [map_le_iff_le_comap,D,closure_le]
      rintro a (rfl | rfl | rfl)
      all_goals
        intro y hy
        obtain rfl := Set.mem_singleton_iff.mp hy
      · exact hi 0
      · exact hi 1
      · exact hi 2
    have hall : (⊤ : Subgroup S) ≤ centralizer ({roots i} : Set S) :=
      hgen ▸ sup_le hD hU
    have hn : ∀ i : Fin 3, ∃ j k : Fin 6,
        roots i * Equiv.swap j k ≠ Equiv.swap j k * roots i := by decide
    obtain ⟨j,k,hjk⟩ := hn i
    exact (hjk (hall (mem_top (Equiv.swap j k)) _ (Set.mem_singleton _))).elim
  · refine ⟨dWords c,dWords_mem c,?_⟩
    apply eq_of_le_of_card_ge
    · rw [map_le_iff_le_comap,map_le_iff_le_comap,D,closure_le]
      rintro a (rfl | rfl | rfl)
      all_goals
        first
        | obtain ⟨k,hk⟩ := hc 0
          exact ⟨roots k,roots_mem k,hk.symm⟩
        | obtain ⟨k,hk⟩ := hc 1
          exact ⟨roots k,roots_mem k,hk.symm⟩
        | obtain ⟨k,hk⟩ := hc 2
          exact ⟨roots k,roots_mem k,hk.symm⟩
    · simp only [card_map_of_injective (f := (MulAut.conj (dWords c)).toMonoidHom) (MulAut.conj (dWords c)).injective,
        card_map_of_injective (f := (MulAut.conj u).toMonoidHom) (MulAut.conj u).injective,
        card_map_of_injective (f := (MulAut.conj opposite).toMonoidHom) (MulAut.conj opposite).injective,le_refl]

private theorem right_standard_generate (u : S)
    (hgen : D ⊔ D.map (MulAut.conj u).toMonoidHom = ⊤)
    (A : Subgroup S) (hA : A ≤ D) (hc : 2 < Nat.card A) :
    D.map (MulAut.conj u).toMonoidHom ⊔ A = ⊤ := by
  obtain ⟨c,hcD,he⟩ := conjugate_plane_coordinates u hgen
  have hD : D.map (MulAut.conj c).toMonoidHom = D :=
    mem_normalizer_iff_map_conj_eq.mp (D.le_normalizer hcD)
  apply map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
  rw [Subgroup.map_sup,he,map_top_of_surjective _ (MulAut.conj c).surjective]
  exact standard_generate _ ((map_mono hA).trans_eq hD)
    (by rwa [card_map_of_injective (MulAut.conj c).injective])
private theorem map_conj_comp (A : Subgroup S) (g k : S) :
    (A.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*k)).toMonoidHom := by
  rw [map_map]
  congr 1

private theorem generating_planes_large_subactor (u v : S)
    (hgen : D.map (MulAut.conj u).toMonoidHom ⊔
      D.map (MulAut.conj v).toMonoidHom = ⊤)
    (A : Subgroup S) (hA : A ≤ D.map (MulAut.conj v).toMonoidHom)
    (hc : 2 < Nat.card A) :
    D.map (MulAut.conj u).toMonoidHom ⊔ A = ⊤ := by
  have hv : (D.map (MulAut.conj v).toMonoidHom).map
      (MulAut.conj v⁻¹).toMonoidHom = D := by
    rw [map_conj_comp,inv_mul_cancel]
    exact Subgroup.map_id D
  have hh := congrArg (Subgroup.map (MulAut.conj v⁻¹).toMonoidHom) hgen
  rw [Subgroup.map_sup,hv,map_conj_comp,map_top_of_surjective _
    (MulAut.conj v⁻¹).surjective,sup_comm] at hh
  have hA' : A.map (MulAut.conj v⁻¹).toMonoidHom ≤ D := (map_mono hA).trans_eq hv
  have hg := right_standard_generate (v⁻¹*u) hh _ hA'
    (by rwa [card_map_of_injective (MulAut.conj v⁻¹).injective])
  apply map_injective (f := (MulAut.conj v⁻¹).toMonoidHom) (MulAut.conj v⁻¹).injective
  rw [Subgroup.map_sup,map_conj_comp,map_top_of_surjective _ (MulAut.conj v⁻¹).surjective]
  exact hg
end PlaneSubactor

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
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
/-- In a generating pair of actual plane edges, any subgroup of the second
edge whose image over the vertex two-core has order greater than two
still generates with the first edge. The same literal vertex and edges
are retained, and the cubic covering kernel is not replaced by the core. -/
theorem plane_edge_pair_large_subactor_generates
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a t s : Vertex Rg} (ha : color Rg a = false)
    (hat : Adjacent Rg a t) (has : Adjacent Rg a s)
    (hgen : Q Rg t ⊔ Q Rg s = stabilizer Rg a)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg s)
    (hlarge : 2 < (Q Rg a).relIndex A) :
    Q Rg t ⊔ A = stabilizer Rg a := by
  obtain ⟨i,hi,hir,hiR,hiQ,_⟩ := remaining_edge_coordinates h e hz ha hat
  obtain ⟨g,hg,hgs⟩ := stabilizer_transitive_neighbors Rg a hat has
  obtain ⟨m,hm⟩ := (show g ∈ i.range from hir.symm ▸ hg)
  let C := (Rg).map (MulAut.conj m⁻¹).toMonoidHom
  have hCi : C.map i = Q Rg s := by
    rw [selection_map_conj i Rg m⁻¹,hiR,map_inv,hm,←Q_act,hgs]
  let A₀ := A.comap i
  have hAi : A₀.map i = A := map_comap_eq_self
    (hA.trans ((show Q Rg s ≤ stabilizer Rg a from
      fun _ hx => hx.2 _ (adjacent_symm Rg has)).trans_eq hir.symm))
  have hAC : A₀ ≤ C := (map_le_map_iff_of_injective hi).mp (by rwa [hAi,hCi])
  have htwo : IsPGroup 2 A₀ :=
    (h.relative_radical.isPGroup.map (MulAut.conj m⁻¹).toMonoidHom).to_le hAC
  have hpair : Rg ⊔ C = ⊤ := by
    apply map_injective hi
    rw [Subgroup.map_sup,hiR,hCi,hgen,←MonoidHom.range_eq_map,hir]
  have hCm : C.map π = D.map (MulAut.conj ((π m)⁻¹*u)).toMonoidHom := by
    rw [selection_map_conj π Rg m⁻¹,hR,map_inv,PlaneSubactor.map_conj_comp]
  have hpairm := congrArg (Subgroup.map π) hpair
  rw [Subgroup.map_sup,hR,hCm,map_top_of_surjective _
    (CubicEven.projection_surjective h e hz hk)] at hpairm
  have hcard : 2 < Nat.card (A₀.map π) := by
    rw [CubicAction.permutation_image_card_of_two h e hz hk A₀ htwo]
    have hh : (pCore 2 M).relIndex A₀ = (Q Rg a).relIndex A := by
      rw [←hiQ,←hAi,relIndex_map_map_of_injective _ _ hi]
    rwa [hh]
  have him : (Rg ⊔ A₀).map π = ⊤ := by
    rw [Subgroup.map_sup,hR]
    exact PlaneSubactor.generating_planes_large_subactor u ((π m)⁻¹*u) hpairm
      (A₀.map π) ((map_mono hAC).trans_eq hCm) hcard
  have hcover : (Rg ⊔ A₀) ⊔ extensionKernel h = ⊤ := by
    have hh := congrArg (Subgroup.comap π) him
    rwa [comap_map_eq,CubicAction.projection_kernel h e hz hk,comap_top] at hh
  have hE := extensionKernel_no_supplement h (Rg ⊔ A₀) (hcover ▸ le_top)
  rw [extensionKernel_twoCore h,
    sup_of_le_left (h.relative_radical.twoCore_le.trans le_sup_left)] at hE
  rw [sup_of_le_left hE] at hcover
  have hh := congrArg (Subgroup.map i) hcover
  rwa [Subgroup.map_sup,hiR,hAi,←MonoidHom.range_eq_map,hir] at hh

include h e hz hk in
/-- The same normalized selector generates with every large subactor of
the original first edge, and with every large subactor of the switched
selected edge. This is the literal first-edge placement used on p.927;
both original generation identities and the component switch are retained. -/
theorem plane_small_critical_subactor_selectors
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
      Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
      Q Rg t ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg (alpha Rg) ∧
      x ∈ normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
      Z Rg z ⊔ Z Rg (act Rg x z) ≤ Q Rg (p.walk.getVert 1) ∧
      (∀ A : Subgroup (FreeAmalgam Rg), A ≤ Q Rg (p.walk.getVert 1) →
        2 < (Q Rg (alpha Rg)).relIndex A →
        Q Rg t ⊔ A = stabilizer Rg (alpha Rg)) ∧
      (∀ A : Subgroup (FreeAmalgam Rg), A ≤ Q Rg (act Rg x t) →
        2 < (Q Rg (alpha Rg)).relIndex A →
        Q Rg t ⊔ A = stabilizer Rg (alpha Rg)) ∧
      (∀ A : Subgroup (FreeAmalgam Rg), A ≤ Q Rg t →
        2 < (Q Rg (alpha Rg)).relIndex A →
        Q Rg (act Rg x t) ⊔ A = stabilizer Rg (alpha Rg)) := by
  obtain ⟨t,hat,r,hr,hgen,hpair,_,hnorm,hinside,_⟩ :=
    remaining_small_critical_normalized_plane_selectors h e hz hk u (Or.inl hR) p hsmall
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have has : Adjacent Rg (alpha Rg) (act Rg x t) := by
    rw [←show act Rg x (alpha Rg) = alpha Rg from hx]
    exact (adjacent_act_iff Rg x _ _).mpr hat
  have hat₀ : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat] at hgen hpair
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl has] at hpair
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat₀] at hnorm hinside
  have hfirst : Q Rg t ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg (alpha Rg) := by
    apply le_antisymm
    · exact sup_le (le_sup_left.trans hpair.le)
        (fun _ hx => hx.2 _ (adjacent_symm Rg hat₀))
    · rw [←hgen]
      exact sup_le (sup_le le_sup_left ((le_sup_left.trans hinside).trans le_sup_right))
        ((le_sup_right.trans hinside).trans le_sup_right)
  exact ⟨t,hat,r,hr,hgen,hpair,hfirst,hnorm,hinside,
    fun A hA hc => plane_edge_pair_large_subactor_generates h e hz hk u hR rfl hat hat₀ hfirst A hA hc,
    fun A hA hc => plane_edge_pair_large_subactor_generates h e hz hk u hR rfl hat has hpair A hA hc,
    fun A hA hc => plane_edge_pair_large_subactor_generates h e hz hk u hR rfl has hat
      ((sup_comm _ _).trans hpair) A hA hc⟩

omit hk in
include h e hz in
/-- The whole-core reduction now supplies the large-subactor generation
clause at every vertex of the original plane graph. -/
theorem coreExhaustion_or_cubic_plane_subactor_generation :
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
        ∀ a t s : Vertex Rg, color Rg a = false →
          Adjacent Rg a t → Adjacent Rg a s →
          Q Rg t ⊔ Q Rg s = stabilizer Rg a →
          ∀ A : Subgroup (FreeAmalgam Rg), A ≤ Q Rg s →
            2 < (Q Rg a).relIndex A → Q Rg t ⊔ A = stabilizer Rg a) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun _ _ _ ha hat has hgen A hA hc =>
        plane_edge_pair_large_subactor_generates h e hz hk u hplane ha hat has hgen A hA hc⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application, preserving both moving covers and the
original Borel alternative. -/
theorem rankTwo_or_cubic_plane_subactor_generation :
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
        ∀ a t s : Vertex Rg, color Rg a = false →
          Adjacent Rg a t → Adjacent Rg a s →
          Q Rg t ⊔ Q Rg s = stabilizer Rg a →
          ∀ A : Subgroup (FreeAmalgam Rg), A ≤ Q Rg s →
            2 < (Q Rg a).relIndex A → Q Rg t ⊔ A = stabilizer Rg a) :=
  (coreExhaustion_or_cubic_plane_subactor_generation h e hz).imp
    (rankTwo_of_exhaustion h e hz) id


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
