module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSubactorGeneration

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPairedSelectors
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardRigidity

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusNormalizer

/-!
# Two displaced full radius kernels do not lie in a common two-group

For two generating plane radicals in S₆, let P be a four-subgroup in the
first radical and g an element of the second. If P and its g-conjugate
generate a two-group, g fixes every transposition in P. The sixteen-entry
cube subgroup catalogue reduces this to short certificates: whenever a
transposition moves, the square of a product of two specified generators
has order three. No group-order or representation catalogue is added.

A faithful edge chart transports this comparison to the original cubic
graph. Fixing the critical transposition normalizes its literal commutator
with the moving seed, because the projection kernel E centralizes that
seed. The full seed has the same commutator: the entire edge attachment
centralizes the actor. Thus the critical commutator, and its join with the
full endpoint center, are preserved. Alignment identifies this central
quotient line with the escaping full radius-kernel line. The previously
proved opposite-edge displacement contradicts that preservation.

At distance four with uniformly small critical images, the same selected
path and opposite edge therefore give a second critical path with the same
endpoint. The two midpoint radius kernels do not generate a two-group;
neither do the two whole last-edge radius kernels. Their individual
endpoint images still have order four. The whole-core and literal C.1.32
applications retain the original radical, both moving covers of orders
sixteen and thirty-two, all central attachments, and the projection kernel
E with its nontrivial odd quotient E/Q.

This is an obstruction to common two-group containment, not the terminal
contradiction of MS93 (5.12). The missing geometric comparison, other image
and distance cases, Borel exclusion and both core exhaustions remain.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the generating-stabilizer comparisons in (5.6) and (5.12), printed
pp.917--918,924--927; Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterB.Offenders.SixCorePlane (cube_eq opposite)
namespace PlaneRadiusPair
private def witness : Fin 16 → Fin 8 → Fin 8 × Fin 8 :=
![
  ![(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  ![(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  ![(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  ![(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  ![(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  ![(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  ![(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  ![(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  ![(0,0),(1,1),(2,2),(1,1),(1,1),(1,2),(1,1),(1,2)],
  ![(0,0),(1,1),(4,4),(1,1),(1,1),(1,4),(1,1),(1,4)],
  ![(0,0),(2,2),(2,2),(2,4),(4,4),(2,2),(2,2),(2,4)],
  ![(0,0),(1,1),(0,0),(1,1),(1,1),(6,6),(1,1),(6,6)],
  ![(0,0),(2,2),(2,2),(5,5),(0,0),(2,2),(2,2),(5,5)],
  ![(0,0),(0,0),(3,3),(3,4),(3,3),(3,4),(3,3),(3,3)],
  ![(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)],
  ![(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)]
]

private def oppositeWord (j : Fin 8) : S := opposite*dWords j*opposite⁻¹
private def witnessElement (r : Fin 16) (j : Fin 8) : S :=
  (dWords (witness r j).1 *
    (oppositeWord j * dWords (witness r j).2 * (oppositeWord j)⁻¹))^2
private theorem certificate : ∀ r j t,
    (dLatticeIndices r).card = 4 → t ∈ dLatticeIndices r →
    (dWords t).support.card = 2 →
    oppositeWord j * dWords t * (oppositeWord j)⁻¹ ≠ dWords t →
    (witness r j).1 ∈ dLatticeIndices r ∧ (witness r j).2 ∈ dLatticeIndices r ∧
      (witnessElement r j)^3 = 1 ∧ witnessElement r j ≠ 1 := by
  intro r j
  fin_cases r <;> fin_cases j <;> decide +kernel

private theorem standard_swap_fixed (P : Subgroup S) (hP : P ≤ D)
    (hcard : Nat.card P = 4) (g t : S)
    (hg : g ∈ D.map (MulAut.conj opposite).toMonoidHom)
    (ht : t ∈ P) (hs : t.IsSwap)
    (htwo : IsPGroup 2 (P ⊔ P.map (MulAut.conj g).toMonoidHom : Subgroup S)) :
    g*t*g⁻¹ = t := by
  obtain ⟨r,rfl⟩ := (subgroup_le_D_iff P).mp (cube_eq ▸ hP)
  obtain ⟨w,hw,rfl⟩ := hg
  obtain ⟨j,rfl⟩ := PlaneSubactor.mem_D hw
  obtain ⟨k,hk,rfl⟩ := (mem_dLattice_iff _ _).mp ht
  change oppositeWord j*dWords k*(oppositeWord j)⁻¹ = dWords k
  by_contra hn
  have hs' : (dWords k).support.card = 2 := Equiv.Perm.card_support_eq_two.mpr hs
  rw [card_dLattice] at hcard
  obtain ⟨ha,hb,hcube,hne⟩ := certificate r j k hcard hk hs' hn
  let J := dLattice r ⊔ (dLattice r).map (MulAut.conj (oppositeWord j)).toMonoidHom
  have hx : witnessElement r j ∈ J :=
    J.pow_mem (J.mul_mem (mem_sup_left ((dWords_mem_dLattice _ _).mpr ha))
      (mem_sup_right (mem_map_of_mem (MulAut.conj (oppositeWord j)).toMonoidHom
        ((dWords_mem_dLattice _ _).mpr hb)))) 2
  have ho : orderOf (⟨witnessElement r j,hx⟩ : J) = 3 :=
    orderOf_eq_prime (Subtype.ext hcube) (fun he => hne (congrArg Subtype.val he))
  change IsPGroup 2 J at htwo
  have hd := htwo.dvd_orderOf (g := (⟨witnessElement r j,hx⟩ : J))
    (fun he => hne (congrArg Subtype.val he))
  rw [ho] at hd
  norm_num at hd
private theorem conjugate_isSwap (g t : S) (ht : t.IsSwap) :
    (g*t*g⁻¹).IsSwap := by
  rcases ht with ⟨a,b,hab,rfl⟩
  rw [←Equiv.swap_apply_apply]
  exact ⟨g a,g b,fun he => hab (g.injective he),rfl⟩

private theorem swap_fixed_of_relabel (g t k : S)
    (hh : (k*g*k⁻¹)*(k*t*k⁻¹)*(k*g*k⁻¹)⁻¹ = k*t*k⁻¹) : g*t*g⁻¹ = t := by
  apply (MulAut.conj k).injective
  change k*(g*t*g⁻¹)*k⁻¹ = k*t*k⁻¹
  calc
    _ = (k*g*k⁻¹)*(k*t*k⁻¹)*(k*g*k⁻¹)⁻¹ := by group
    _ = _ := hh

private theorem right_swap_fixed (v : S)
    (hgen : D ⊔ D.map (MulAut.conj v).toMonoidHom = ⊤)
    (P : Subgroup S) (hP : P ≤ D) (hcard : Nat.card P = 4) (g t : S)
    (hg : g ∈ D.map (MulAut.conj v).toMonoidHom)
    (ht : t ∈ P) (hs : t.IsSwap)
    (htwo : IsPGroup 2 (P ⊔ P.map (MulAut.conj g).toMonoidHom : Subgroup S)) :
    g*t*g⁻¹ = t := by
  obtain ⟨c,hc,he⟩ := PlaneSubactor.conjugate_plane_coordinates v hgen
  let f := (MulAut.conj c).toMonoidHom
  have hD : D.map f = D := mem_normalizer_iff_map_conj_eq.mp (D.le_normalizer hc)
  have hp := htwo.map f
  rw [Subgroup.map_sup,CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull.selection_map_conj] at hp
  have hh := standard_swap_fixed (P.map f) ((map_mono hP).trans_eq hD)
    (by rwa [card_map_of_injective (MulAut.conj c).injective]) (f g) (f t)
    (he ▸ mem_map_of_mem f hg) (mem_map_of_mem f ht) (conjugate_isSwap c t hs) hp
  exact swap_fixed_of_relabel g t c hh

private theorem generating_pair_swap_fixed (u v : S)
    (hgen : D.map (MulAut.conj u).toMonoidHom ⊔
      D.map (MulAut.conj v).toMonoidHom = ⊤)
    (P : Subgroup S) (hP : P ≤ D.map (MulAut.conj u).toMonoidHom)
    (hcard : Nat.card P = 4) (g t : S)
    (hg : g ∈ D.map (MulAut.conj v).toMonoidHom)
    (ht : t ∈ P) (hs : t.IsSwap)
    (htwo : IsPGroup 2 (P ⊔ P.map (MulAut.conj g).toMonoidHom : Subgroup S)) :
    g*t*g⁻¹ = t := by
  let f := (MulAut.conj u⁻¹).toMonoidHom
  have hD : (D.map (MulAut.conj u).toMonoidHom).map f = D := by
    rw [PlaneSubactor.map_conj_comp,inv_mul_cancel]
    exact Subgroup.map_id D
  have hE : (D.map (MulAut.conj v).toMonoidHom).map f =
      D.map (MulAut.conj (u⁻¹*v)).toMonoidHom := PlaneSubactor.map_conj_comp _ _ _
  have hgen' := congrArg (Subgroup.map f) hgen
  rw [Subgroup.map_sup,hD,hE,map_top_of_surjective _ (MulAut.conj u⁻¹).surjective] at hgen'
  have hp := htwo.map f
  rw [Subgroup.map_sup,CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull.selection_map_conj] at hp
  have hh := right_swap_fixed (u⁻¹*v) hgen' (P.map f) ((map_mono hP).trans_eq hD)
    (by rwa [card_map_of_injective (MulAut.conj u⁻¹).injective]) (f g) (f t)
    (hE ▸ mem_map_of_mem f hg) (mem_map_of_mem f ht) (conjugate_isSwap u⁻¹ t hs) hp
  exact swap_fixed_of_relabel g t u⁻¹ hh

end PlaneRadiusPair

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.NormalElementaryQuotient
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
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz in
private theorem full_seed_commutator_eq_moving
    {z t : Vertex Rg} (hzcol : color Rg z = false) (hzt : Adjacent Rg z t)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ Q Rg t) :
    ⁅Z Rg z,A⁆ = ⁅U Rg z,A⁆ := by
  have hh := full_fixed_seed_edge_commutator h e hz hzcol hzt
    (⊥ : Subgroup (FreeAmalgam Rg)) bot_le A hA
  have hb : centralizer ((⊥ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) = ⊤ := by
    apply top_unique
    intro x _ y hy
    have hy1 : y = 1 := mem_bot.mp hy
    simp only [hy1,mul_one,one_mul]
  simpa only [hb,inf_top_eq] using hh

include h e hz hk in
/-- A displaced critical line prevents the original four-image subactor and
its opposite-edge conjugate from lying in a common two-subgroup. The center
in the displacement condition is the full endpoint center. -/
theorem plane_displaced_line_pair_not_two
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {z t s : Vertex Rg} (hzcol : color Rg z = false)
    (hzt : Adjacent Rg z t) (hzs : Adjacent Rg z s)
    (hgen : Q Rg t ⊔ Q Rg s = stabilizer Rg z)
    (A P H : Subgroup (FreeAmalgam Rg))
    (hAP : A ≤ P) (hPt : P ≤ Q Rg t) (hne : ¬ A ≤ Q Rg z)
    (hfix : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg z) ≤ 2)
    (hindex : (Q Rg z).relIndex P = 4)
    (halign : H ⊔ (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) =
      ⁅Z Rg z,A⁆ ⊔ (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))))
    (g : FreeAmalgam Rg) (hgs : g ∈ Q Rg s)
    (hsep : H.map (MulAut.conj g).toMonoidHom ⊔
        (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) ≠
      H ⊔ (stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)))) :
    ¬ IsPGroup 2 (P ⊔ P.map (MulAut.conj g).toMonoidHom : Subgroup (FreeAmalgam Rg)) := by
  intro htwo
  let := h.relative_normal
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := remaining_edge_coordinates h e hz hzcol hzt
  obtain ⟨k,hkz,hks⟩ := stabilizer_transitive_neighbors Rg z hzt hzs
  obtain ⟨n,hn⟩ := (show k ∈ i.range from hir.symm ▸ hkz)
  let C := (Rg).map (MulAut.conj n⁻¹).toMonoidHom
  have hCi : C.map i = Q Rg s := by
    rw [selection_map_conj i Rg n⁻¹,hiR,map_inv,hn,←Q_act,hks]
  have hpair : Rg ⊔ C = ⊤ := by
    apply map_injective hi
    rw [Subgroup.map_sup,hiR,hCi,hgen,←MonoidHom.range_eq_map,hir]
  have hCm : C.map π = D.map (MulAut.conj ((π n)⁻¹*u)).toMonoidHom := by
    rw [selection_map_conj π Rg n⁻¹,hR,map_inv,PlaneSubactor.map_conj_comp]
  have hpairm := congrArg (Subgroup.map π) hpair
  rw [Subgroup.map_sup,hR,hCm,map_top_of_surjective _
    (CubicEven.projection_surjective h e hz hk)] at hpairm
  have hgz : g ∈ stabilizer Rg z := hgs.2 _ (adjacent_symm Rg hzs)
  obtain ⟨m,hm⟩ := (show g ∈ i.range from hir.symm ▸ hgz)
  have hmC : m ∈ C := by
    obtain ⟨v,hv,hv'⟩ := hCi.symm ▸ hgs
    exact hi (hv'.trans hm.symm) ▸ hv
  let A₀ := A.comap i
  let P₀ := P.comap i
  have hPi : P₀.map i = P := map_comap_eq_self
    (hPt.trans (hiR ▸ map_le_range i _))
  have hAi : A₀.map i = A := map_comap_eq_self
    ((hAP.trans hPt).trans (hiR ▸ map_le_range i _))
  have hPr : P₀ ≤ Rg := (map_le_map_iff_of_injective hi).mp (by rwa [hPi,hiR])
  have hAr : A₀ ≤ Rg := (comap_mono hAP).trans hPr
  have hAn : ¬ A₀ ≤ pCore 2 M := by
    intro hh
    apply hne
    have hh' := map_mono (f := i) hh
    rwa [hAi,hiQ] at hh'
  have hidx : (centralizer (A₀ : Set M)).relIndex W₀ ≤ 2 := by
    rw [←hiU,←hAi,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hfix
    exact hfix
  have hsmall : fixedCodim (coverAction h e hz hk) (A₀.map π) ≤ 1 := by
    rw [centralizer_index_eq_fixedCodim W₀ π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)] at hidx
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hidx
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A₀.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk) (naturalRepresentation (Fin 6))
      (coverMap h e hz hk) (coverMap_surjective h e hz hk)
      (coverMap_equivariant h e hz hk) (A₀.map π)).trans hsmall
  have hAne : A₀.map π ≠ ⊥ := by
    intro he
    exact hAn (two_subgroup_le_core_of_le_extensionKernel h hz A₀
      (h.relative_radical.isPGroup.to_le hAr)
      (CubicAction.projection_kernel h e hz hk ▸ (map_eq_bot_iff A₀).mp he))
  obtain ⟨v,hv,hvs,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers (A₀.map π) hAne hnat
  have hcard : Nat.card (P₀.map π) = 4 := by
    rw [CubicAction.permutation_image_card_of_two h e hz hk P₀
      (h.relative_radical.isPGroup.to_le hPr)]
    rwa [←hiQ,←hPi,relIndex_map_map_of_injective _ _ hi] at hindex
  have hlocal : P₀ ⊔ P₀.map (MulAut.conj m).toMonoidHom ≤
      (P ⊔ P.map (MulAut.conj g).toMonoidHom).comap i := by
    apply (map_le_iff_le_comap).mp
    rw [Subgroup.map_sup,selection_map_conj,hPi,hm]
  have hp := ((htwo.comap_of_injective i hi).to_le hlocal).map π
  rw [Subgroup.map_sup,selection_map_conj] at hp
  have hvt := PlaneRadiusPair.generating_pair_swap_fixed u ((π n)⁻¹*u) hpairm
    (P₀.map π) ((map_mono hPr).trans_eq hR) hcard (π m) v
    (hCm ▸ mem_map_of_mem π hmC) ((map_mono (comap_mono hAP)) hv) hvs hp
  have hactor : A₀.map π ≤ centralizer ({π m} : Set S) := by
    rw [he]
    apply zpowers_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact mul_inv_eq_iff_eq_mul.mp hvt
  have hnormal := commutator_normalized_of_image_centralized π W₀ A₀ m
    (CubicAction.moved_projection_kernel h e hz hk).le hactor
  have hnormal' := le_normalizer_map i (mem_map_of_mem i hnormal)
  rw [map_commutator,hiU,hAi,hm,
    ←full_seed_commutator_eq_moving h e hz hzcol hzt A (hAP.trans hPt)] at hnormal'
  let Zc := stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  have hZc : Zc.map (MulAut.conj g).toMonoidHom = Zc := by
    apply mem_normalizer_iff_map_conj_eq.mp
    apply Subgroup.centralizer_le_normalizer
    exact (le_centralizer_iff.mp (show Zc ≤ centralizer
      (stabilizer Rg z : Set (FreeAmalgam Rg)) from inf_le_right)) hgz
  apply hsep
  calc
    H.map (MulAut.conj g).toMonoidHom ⊔ Zc =
        (H ⊔ Zc).map (MulAut.conj g).toMonoidHom := by rw [Subgroup.map_sup,hZc]
    _ = (⁅Z Rg z,A⁆ ⊔ Zc).map (MulAut.conj g).toMonoidHom := congrArg _ halign
    _ = ⁅Z Rg z,A⁆ ⊔ Zc := by
      have hh : (⁅Z Rg z,A⁆ : Subgroup (FreeAmalgam Rg)).map
          (MulAut.conj g).toMonoidHom = ⁅Z Rg z,A⁆ :=
        mem_normalizer_iff_map_conj_eq.mp hnormal'
      rw [Subgroup.map_sup,hZc,hh]
    _ = H ⊔ Zc := halign.symm

include h e hz hk in
/-- The same opposite-edge displacement produces two critical paths with a
common endpoint whose midpoint radius kernels cannot lie in a common
two-subgroup. The same holds for the two whole last-edge radius kernels. -/
theorem plane_small_four_radius_pair_not_two
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
      let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
      ∃ s, Adjacent Rg z s ∧ Q Rg s ⊔ Y = stabilizer Rg z ∧
        (Q Rg z).relIndex Y = 4 ∧ (Q Rg z).relIndex W = 4 ∧
        ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
            (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
            ¬ IsPGroup 2 (Y ⊔ (V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2)) :
              Subgroup (FreeAmalgam Rg)) ∧
            ¬ IsPGroup 2 (W ⊔ (V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 3)) :
              Subgroup (FreeAmalgam Rg)) := by
  obtain ⟨a,z,p,s,hzs,hgen,hgenY,_,hiY,hiW,_,hcard,hHZ,hHlast,hHC,
    _,_,_,_,_,_,_,_,hescape⟩ := plane_small_four_radius_growth h e hz hk u hR hb4 hsmall
  let c := p.walk.getVert 2
  let t := p.walk.getVert 3
  let Y := V Rg a ⊓ Q Rg c
  let W := V Rg a ⊓ Q Rg t
  let H := ⁅Y,X Rg z ⊓ Q Rg a⁆
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent Rg c t :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z t := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hzt
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have hYt : Y ≤ Q Rg t := inf_le_right.trans (Q_le_adjacent_h Rg ht hct)
  have hYW : Y ≤ W := le_inf inf_le_left hYt
  have hAY : Z Rg a ≤ Y := by
    refine le_inf (Z_le_VBall Rg _ 2) ?_
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.start_color)
    rw [(sourceGeometry h).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact distance_gt_two h e hz hk
  have hXZ := (plane_small_four_omega_generated h e hz hk u hR hb4 hsmall z p.end_color).2
  have hnot : ¬ ⁅Y,Z Rg z⁆ ≤ Z Rg a := by rwa [←hXZ]
  obtain ⟨_,_,_,_,hdis,halign⟩ := plane_radius_kernel_alignment h e hz hk u hR p
    (hsmall _ _ p) Y inf_le_left (by simpa only [hl,Nat.reduceSub] using hYt) hAY hnot
  rw [←hXZ] at hdis halign
  change H ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) = ⊥ at hdis
  have hpair : Q Rg t ⊔ Q Rg s = stabilizer Rg z := (sup_comm _ _).trans hgen
  have hmix := plane_generating_edge_mixed_commutator h e hz hk u hR
    p.end_color hzt hzs hpair H Y hHlast hcard hdis hYt hiY
  have hHY : H ≤ centralizer (Y : Set (FreeAmalgam Rg)) :=
    hHC.trans (centralizer_le (show Y ≤ V Rg a ⊔ V Rg c from
      inf_le_left.trans le_sup_left))
  obtain ⟨g,hgs,hgY⟩ := exists_conjugate_not_centralizing H (Q Rg s) Y hHY hmix
  let C := stabilizer Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))
  have hsep : H.map (MulAut.conj g).toMonoidHom ⊔ C ≠ H ⊔ C := by
    intro he
    apply hgY
    apply (show H.map (MulAut.conj g).toMonoidHom ≤ H ⊔ C from he ▸ le_sup_left).trans
    exact sup_le hHY (inf_le_right.trans (centralizer_le
      (hYt.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hzt)))))
  let := finite_Z Rg z
  let : Finite (U Rg z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
  have hQC := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q Rg a p.start_color))
  have hfix : (centralizer (Z Rg a : Set (FreeAmalgam Rg))).relIndex (U Rg z) ≤ 2 :=
    ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p (hsmall _ _ p)).2
  have halign' : H ⊔ C = ⁅Z Rg z,Z Rg a⁆ ⊔ C := by
    rw [commutator_comm (Z Rg z)]
    change H ⊔ C = ⁅Z Rg a,X Rg z⁆ ⊔ C at halign
    rwa [hXZ] at halign
  have hYtwo := plane_displaced_line_pair_not_two h e hz hk u hR p.end_color hzt hzs hpair
    (Z Rg a) Y H hAY hYt p.critical.2 hfix hiY halign' g hgs hsep
  have hWtwo : ¬ IsPGroup 2 (W ⊔ W.map (MulAut.conj g).toMonoidHom : Subgroup (FreeAmalgam Rg)) :=
    fun hh => hYtwo (hh.to_le (sup_le_sup hYW (map_mono hYW)))
  have hfixz : act Rg g⁻¹ z = z :=
    (stabilizer Rg z).inv_mem (hgs.2 _ (adjacent_symm Rg hzs))
  have hq : ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
      ∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i) := by
    have hh : ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) (act Rg g⁻¹ z),
        ∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i) := by
      refine ⟨p.act g⁻¹,?_⟩
      intro i
      simp only [CriticalPath.act,actWalk_getVert]
    let P := fun w : Vertex Rg =>
      ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) w,
        ∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)
    exact (congrArg P hfixz).mp hh
  obtain ⟨q,hverts⟩ := hq
  refine ⟨a,z,p,s,hzs,hgenY,hiY,hiW,g,hgs,hfixz,q,hverts,?_,?_⟩
  · rw [hverts 2,V_act,Q_act,inv_inv,
      ←Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    exact hYtwo
  · rw [hverts 3,V_act,Q_act,inv_inv,
      ←Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
    exact hWtwo

omit hk in
include h e hz in
/-- The original whole-core reduction supplies the two critical paths and
both failures of common two-group containment in the small distance-four
plane branch. Both covering modules and the Borel branch are retained. -/
theorem coreExhaustion_or_cubic_plane_radius_pair :
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
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
            ∃ s, Adjacent Rg z s ∧ Q Rg s ⊔ Y = stabilizer Rg z ∧
              (Q Rg z).relIndex Y = 4 ∧ (Q Rg z).relIndex W = 4 ∧
              ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
                ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
                  (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
                  ¬ IsPGroup 2 (Y ⊔ (V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2)) :
                    Subgroup (FreeAmalgam Rg)) ∧
                  ¬ IsPGroup 2 (W ⊔ (V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 3)) :
                    Subgroup (FreeAmalgam Rg)))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall => plane_small_four_radius_pair_not_two h e hz hk u hplane hb4 hsmall⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application through the original cubic projection. The
paired-kernel conclusion retains its distance-four and small-image premises. -/
theorem rankTwo_or_cubic_plane_radius_pair :
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
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∃ a z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
            let Y := V Rg a ⊓ Q Rg (p.walk.getVert 2)
            let W := V Rg a ⊓ Q Rg (p.walk.getVert 3)
            ∃ s, Adjacent Rg z s ∧ Q Rg s ⊔ Y = stabilizer Rg z ∧
              (Q Rg z).relIndex Y = 4 ∧ (Q Rg z).relIndex W = 4 ∧
              ∃ g ∈ Q Rg s, act Rg g⁻¹ z = z ∧
                ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg g⁻¹ a) z,
                  (∀ i, q.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
                  ¬ IsPGroup 2 (Y ⊔ (V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 2)) :
                    Subgroup (FreeAmalgam Rg)) ∧
                  ¬ IsPGroup 2 (W ⊔ (V Rg (act Rg g⁻¹ a) ⊓ Q Rg (q.walk.getVert 3)) :
                    Subgroup (FreeAmalgam Rg)))) :=
  (coreExhaustion_or_cubic_plane_radius_pair h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
