module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneEndSlices
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFourExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRemainingRadicals

/-!
# Paired endpoint control on the original selected cubic span

Let P be the selected orbit span and Y its intersection with the opposite
two-core. If P is nonabelian and Y has index at most two in P, every
two-subgroup A satisfying [Y,A] <= Z_alpha has image of order at most two
under the original cubic projection. Indeed, a nontrivial even part of
that image contains an involution. It fixes a hyperplane in P/Z(P), whereas
the faithful component action requires it to move at least two dimensions.
The sign map is therefore injective on the image. This argument retains
the odd kernel E/Q and does not assume that A itself is elementary abelian.

For the two small critical endpoints supplied by the original selector,
the generation identity makes their critical lines distinct. If their joint
image had order at most two, their transposition images would coincide.
Lifting through E, which centralizes the full starting seed, would identify
the two critical lines. Consequently the common-core subgroup Y cannot
satisfy the endpoint commutator estimate for both selected endpoints.

At distance four, the two literal end-slice bounds supply nonabelianness
and the common-core index bound on the same original span. They also give
[Y,Z_endpoint intersect Q_alpha] = 1: this commutator lies in the derived
line of P and is fixed at the midpoint, whereas that line has order two and
is not fixed there. The full critical-kernel calculation then proves
[Y,Z_endpoint] <= Z_alpha. Applying the paired comparison forces failure
of the estimate at the shifted endpoint. The application retains the same
span, switch, full walk transport, both generation identities, and the
first-edge containment.
The whole-core and literal C.1.32 consumers retain both covers and the Borel
branch. This proves the paired-action comparison used in the source's
clause (3); it does not establish that clause's slice bounds or the remaining
shifted-path commutator estimate. The remaining source path comparisons,
larger-distance and Borel exclusions, and both core exhaustions remain.

The internal imports reuse the existing central-quotient action and
selector calculations without changing their public boundaries.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the use of (1.4) in (5.12)(3), printed pp.926--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
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
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
/-- A controlled two-subgroup has image of order at most two in the original
cubic quotient, measured through E rather than by discarding E/Q. -/
theorem selected_span_controlled_two_image
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hnon : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥)
    (hindex : (Q Rg (p.walk.getVert 2)).relIndex
      (localZSpan Rg (p.walk.getVert 2) (alpha Rg)) ≤ 2)
    (A : Subgroup (FreeAmalgam Rg))
    (htwo : IsPGroup 2 A)
    (hcomm : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓
      Q Rg (p.walk.getVert 2),A⁆ ≤ Z Rg (alpha Rg)) :
    Nat.card ((A.comap (embedM Rg)).map π) ≤ 2 := by
  have hb := distance_gt_two h e hz hk
  have hd : (cosetGraph Rg).dist (p.walk.getVert 2) (alpha Rg) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by
      have hl : p.walk.length = sourceDistance h := p.length_eq_b
      omega)]
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  have hPG : P ≤ stabilizer Rg (alpha Rg) :=
    (localZSpan_le_V Rg hd).trans ((sourceGeometry h).V_local _ rfl hb)
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  let := selected_span_central_quotient_elementary h e hz hk hb (p.walk.getVert 2) hd
  let ρ := forwardSpanCentralAction Rg (p.walk.getVert 2)
  let σ := Offenders.linearize ρ
  have hker : σ.ker ≤ (π).ker := by
    rw [CubicAction.projection_kernel]
    apply le_trans ?_ (selected_span_central_action_kernel_le_extension h e hz hk hb p hnon)
    intro m hm
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro v
    exact congrArg Additive.toMul (LinearMap.congr_fun hm (Additive.ofMul v))
  let A₀ := (A.comap (embedM Rg)).map π
  have hA₀ : IsPGroup 2 A₀ :=
    (htwo.comap_of_injective (embedM Rg) (embedM_injective Rg)).map π
  let C := A₀ ⊓ alternatingGroup (Fin 6)
  have hC : Nat.card C = 1 := by
    rcases (hA₀.to_le (show C ≤ A₀ from inf_le_left)).card_eq_or_dvd with hc | hc
    · exact hc
    obtain ⟨a,ha2⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hc
    have ha : orderOf (a : S) = 2 := (orderOf_injective C.subtype C.subtype_injective a).trans ha2
    obtain ⟨m,hm,heq⟩ := a.property.1
    have hi := selected_span_actor_fixed_index h hb p hd hindex A hcomm m hm
    have hup := linearized_cyclic_codim_le_one ρ m hi
    have hlo := EvenLift.fixedCodim_lower π (CubicEven.projection_surjective h e hz hk)
      σ hker m (heq.symm ▸ a.property.2) (heq.symm ▸ ha)
    change fixedCodim σ (zpowers m) ≤ 1 at hup
    omega
  let f := (Equiv.Perm.sign (α := Fin 6)).comp A₀.subtype
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro a ha
    apply Subtype.ext
    exact mem_bot.mp ((card_eq_one.mp hC) ▸ (show (a : S) ∈ C from ⟨a.property,ha⟩))
  have hc := Nat.card_le_card_of_injective f hf
  have htwo : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card,Fintype.card_units_int]
  rw [htwo] at hc
  exact hc

include h e hz hk in
private theorem critical_lines_eq_of_images_eq
    {z z' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (him : ((Z Rg z).comap (embedM Rg)).map π =
      ((Z Rg z').comap (embedM Rg)).map π) :
    ⁅Z Rg (alpha Rg),Z Rg z⁆ = ⁅Z Rg (alpha Rg),Z Rg z'⁆ := by
  have hpG := critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
    (sourceDistance_pos h) p.critical
  have hqG := critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
    (sourceDistance_pos h) q.critical
  have hpmap : ((Z Rg z).comap (embedM Rg)).map (embedM Rg) = Z Rg z :=
    map_comap_eq_self (hpG.trans_eq (stabilizer_m_base Rg))
  have hqmap : ((Z Rg z').comap (embedM Rg)).map (embedM Rg) = Z Rg z' :=
    map_comap_eq_self (hqG.trans_eq (stabilizer_m_base Rg))
  have hZmap : (radiusSeed L R).map (embedM Rg) = Z Rg (alpha Rg) :=
    map_comap_eq_self ((Z_le_stabilizer Rg _).trans_eq (stabilizer_m_base Rg))
  let E := (extensionKernel h).map (embedM Rg)
  have hEC : E ≤ centralizer (Z Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    rintro _ ⟨m,hm,rfl⟩ y hy
    rw [←hZmap] at hy
    obtain ⟨v,hv,rfl⟩ := hy
    rw [←seed_centralizer h e hz hk] at hm
    simpa only [map_mul] using congrArg (embedM Rg) (hm v hv)
  have hj := congrArg (Subgroup.comap π) him
  rw [comap_map_eq,comap_map_eq,CubicAction.projection_kernel h e hz hk] at hj
  have hj' := congrArg (Subgroup.map (embedM Rg)) hj
  rw [Subgroup.map_sup,Subgroup.map_sup,hpmap,hqmap] at hj'
  have hjoin : E ⊔ Z Rg z = E ⊔ Z Rg z' :=
    (sup_comm _ _).trans (hj'.trans (sup_comm _ _))
  exact (commutator_eq_of_centralizing_sup rfl hEC (hpG.trans (Z_normalized Rg _))).trans
    ((congrArg (fun K => ⁅Z Rg (alpha Rg),K⁆) hjoin).trans
      (commutator_eq_of_centralizing_sup rfl hEC (hqG.trans (Z_normalized Rg _))).symm)

include h e hz hk in
/-- On one nonabelian selected span of common-core index at most two, the
source-selected small critical endpoints cannot both satisfy kernel control. -/
theorem selected_span_paired_critical_escape
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom ∨
      (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z z' t t₀ : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (q : CriticalPath Rg (sourceGeometry h) (alpha Rg) z')
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hq : (Q Rg z').relIndex (Z Rg (alpha Rg)) < 4)
    (hnon : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥)
    (hindex : (Q Rg (p.walk.getVert 2)).relIndex
      (localZSpan Rg (p.walk.getVert 2) (alpha Rg)) ≤ 2)
    (hat : Adjacent Rg (alpha Rg) t) (hat₀ : Adjacent Rg (alpha Rg) t₀)
    (hgen : (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg z' =
      stabilizer Rg (alpha Rg))
    (hinside : Z Rg z ⊔ Z Rg z' ≤ edgeOffenderJoin (alpha Rg) t₀) :
    let Y := localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓ Q Rg (p.walk.getVert 2)
    ¬ ⁅Y,Z Rg z⁆ ≤ Z Rg (alpha Rg) ∨ ¬ ⁅Y,Z Rg z'⁆ ≤ Z Rg (alpha Rg) := by
  dsimp only
  by_contra! hboth
  let Y := localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓ Q Rg (p.walk.getVert 2)
  let A := Z Rg z ⊔ Z Rg z'
  have hpG := critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
    (sourceDistance_pos h) p.critical
  have hqG := critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
    (sourceDistance_pos h) q.critical
  have hcomm : ⁅Y,A⁆ ≤ Z Rg (alpha Rg) := by
    rw [commutator_comm]
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      (Z Rg z) (Z Rg z') Y (Z Rg (alpha Rg)) (Z_normalized Rg _) hpG hqG
    · rw [commutator_comm]; exact hboth.1
    · rw [commutator_comm]; exact hboth.2
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := remaining_edge_coordinates h e hz rfl hat₀
  have hAR : A ≤ Q Rg t₀ := hinside.trans
    (remaining_edge_thompson h e hz hk u hR rfl hat₀).2.2.1
  have htwo : IsPGroup 2 A :=
    (hiR ▸ h.relative_radical.isPGroup.map i).to_le hAR
  let A₀ := (A.comap (embedM Rg)).map π
  let A₁ := ((Z Rg z).comap (embedM Rg)).map π
  let A₂ := ((Z Rg z').comap (embedM Rg)).map π
  have hcard : Nat.card A₀ ≤ 2 :=
    selected_span_controlled_two_image h e hz hk p hnon hindex A htwo hcomm
  have h₁ : A₁ ≤ A₀ := map_mono (comap_mono le_sup_left)
  have h₂ : A₂ ≤ A₀ := map_mono (comap_mono le_sup_right)
  obtain ⟨a,ha,him⟩ := small_critical_image_eq_swap h e hz hk p hp
  have hcard₁ : Nat.card A₁ = 2 := by
    dsimp only [A₁]
    rw [him,Nat.card_zpowers,ha.orderOf]
  obtain ⟨b,hb,him'⟩ := small_critical_image_eq_swap h e hz hk q hq
  have hcard₂ : Nat.card A₂ = 2 := by
    dsimp only [A₂]
    rw [him',Nat.card_zpowers,hb.orderOf]
  have he₁ : A₁ = A₀ := eq_of_le_of_card_ge h₁ (by omega)
  have he₂ : A₂ = A₀ := eq_of_le_of_card_ge h₂ (by omega)
  exact paired_small_lines_ne h e hz hk u hR p q hp hq hat hgen
    (critical_lines_eq_of_images_eq h e hz hk p q (he₁.trans he₂.symm))

include h e hz hk in
/-- The two end slices control the entire selected common-core subgroup at
the original endpoint. Its commutator with the full reverse critical kernel
lies in the derived line and is fixed at the midpoint, hence vanishes. -/
theorem plane_four_selected_kernel_endpoint_control
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hforward : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (hopposite : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg z) ≤ 2) :
    let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
    let Y := P ⊓ Q Rg (p.walk.getVert 2)
    ⁅Y,Z Rg z ⊓ Q Rg (alpha Rg)⁆ = ⊥ ∧ ⁅Y,Z Rg z⁆ ≤ Z Rg (alpha Rg) := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hpre : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2 := by
    simpa only [hl,Nat.reduceSub] using hopposite
  have hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [(critical_predecessor_small_slice h e hz hk hb p hpre).2.2]
    decide
  have hn := plane_four_selected_span_nonabelian_of_slices h e hz hk u hR hb4 p
    hforward hopposite
  let c := p.walk.getVert 2
  let P := localZSpan Rg c (alpha Rg)
  let Y := P ⊓ Q Rg c
  let K := Z Rg z ⊓ Q Rg (alpha Rg)
  have hd := small_selected_span_derived h e hz hk hb p hp hforward hn
  have hcentral := (plane_predecessor_slice_commutator_central h e hz hk u hR p hpre).2.2
  simp only [hl,Nat.reduceSub] at hcentral
  have hfixed : ⁅Y,K⁆ ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl (show Y ≤ Q Rg c from inf_le_right)).trans hcentral
  have hline : ⁅Y,K⁆ ≤ ⁅P,P⁆ := by
    rw [hd.1]
    have hh := (small_selected_span_forward_commutator h e hz hk hb p hp hforward).1
    rw [←hh]
    exact commutator_mono inf_le_left
      (le_sup_right.trans (selected_forward_kernel_contains_inner_layers h hb p))
  have hnoncentral : ¬ ⁅P,P⁆ ≤
      centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
    intro hc
    obtain ⟨_,x,hx,q,_,_,_⟩ := selected_span_conjugate_critical_path h hb p hn
    have hstart : Z Rg c ≤ P := Z_le_localZSpan Rg _ _
    have hend : Z Rg (act Rg x c) ≤ P := by
      rw [Z_act]
      exact (map_mono hstart).trans_eq (mem_normalizer_iff_map_conj_eq.mp
        (localZSpan_normalized Rg c (alpha Rg)
          ((stabilizer Rg (alpha Rg)).inv_mem hx)))
    exact critical_commutator_not_central h e hz hk q
      ((commutator_mono hstart hend).trans hc)
  have hcard : Nat.card (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) = 2 := hd.2.1
  let : Finite (⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let : Finite (⁅Y,K⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hline) (inclusion_injective _)
  have hzero : ⁅Y,K⁆ = ⊥ := by
    by_contra hne
    have hlo := (one_lt_card_iff_ne_bot _).mpr hne
    have heq : ⁅Y,K⁆ = ⁅P,P⁆ := eq_of_le_of_card_ge hline (by omega)
    exact hnoncentral (heq ▸ hfixed)
  refine ⟨hzero,?_⟩
  apply small_critical_predecessor_commutator h e hz hk hb p hp Y
  · simpa only [hl,Nat.reduceSub] using (show Y ≤ Q Rg c from inf_le_right)
  · exact commutator_eq_bot_iff_le_centralizer.mp hzero

include h e hz hk in
/-- The two end slices supply the original endpoint estimate on the entire
selected common-core subgroup. The same-switch paired comparison forces
failure at the shifted endpoint, retaining both generation identities. -/
theorem plane_four_selected_pair_of_slices
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hforward : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (hopposite : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg z) ≤ 2) :
    let Y := localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓ Q Rg (p.walk.getVert 2)
    ⁅Y,Z Rg z ⊓ Q Rg (alpha Rg)⁆ = ⊥ ∧ ⁅Y,Z Rg z⁆ ≤ Z Rg (alpha Rg) ∧
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) =
          stabilizer Rg (alpha Rg) ∧
        edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) =
          stabilizer Rg (alpha Rg) ∧
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) :
          Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
        ¬ ⁅Y,Z Rg (act Rg x z)⁆ ≤ Z Rg (alpha Rg) := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4 := by
    have hs := critical_predecessor_small_slice h e hz hk hb p
      (by simpa only [hl,Nat.reduceSub] using hopposite)
    rw [hs.2.2]
    decide
  have hnon := plane_four_selected_span_nonabelian_of_slices h e hz hk u hR hb4 p
    hforward hopposite
  have hindex := (selected_span_index_of_forward_slice h e hz hk hb p hforward).2
  obtain ⟨t,hat,r,hr,hgen,hpair,hfixed,hnorm,hinside,hquad⟩ :=
    remaining_small_critical_normalized_plane_selectors h e hz hk u (Or.inl hR) p hp
  let x := (embedM Rg r)⁻¹
  have hxG : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hxa : act Rg x (alpha Rg) = alpha Rg := hxG
  have hpact : ∃ q : CriticalPath Rg (sourceGeometry h)
      (act Rg x (alpha Rg)) (act Rg x z),
      ∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i) :=
    ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hxa] at hpact
  obtain ⟨q,hqverts⟩ := hpact
  have hq : (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hxa,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hp
  have hat₀ : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hc := plane_four_selected_kernel_endpoint_control h e hz hk u hR hb4 p hforward hopposite
  have he := selected_span_paired_critical_escape h e hz hk u (Or.inl hR) p q hp hq
    hnon hindex hat hat₀ hgen hinside
  exact ⟨hc.1,hc.2,t,hat,r,hr,q,hqverts,hgen,hpair,hnorm,hinside,
    he.resolve_left (fun hbad => hbad hc.2)⟩


omit hk in
include h e hz in
/-- Whole-core application of the selected-pair control obstruction, with
both actual generation identities and the original graph retained. -/
theorem coreExhaustion_or_cubic_plane_pair_control :
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
        (sourceDistance h = 4 → ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ≤ 2 →
          (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg z) ≤ 2 →
          let Y := localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓ Q Rg (p.walk.getVert 2)
          ⁅Y,Z Rg z ⊓ Q Rg (alpha Rg)⁆ = ⊥ ∧ ⁅Y,Z Rg z⁆ ≤ Z Rg (alpha Rg) ∧
          ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
            let x := (embedM Rg r)⁻¹
            ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
              (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
              (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) =
                stabilizer Rg (alpha Rg) ∧
              edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) =
                stabilizer Rg (alpha Rg) ∧
              x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) :
                Set (FreeAmalgam Rg)) ∧
              Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
              ¬ ⁅Y,Z Rg (act Rg x z)⁆ ≤ Z Rg (alpha Rg))) := by
  rcases coreExhaustion_or_cubic_plane_terminal_slices h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 z p hf ho => plane_four_selected_pair_of_slices h e hz hk u hplane hb4 p hf ho⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 consumer of the original selected-pair comparison. -/
theorem rankTwo_or_cubic_plane_pair_control :
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
        (sourceDistance h = 4 → ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (p.walk.getVert 2)) ≤ 2 →
          (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg z) ≤ 2 →
          let Y := localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓ Q Rg (p.walk.getVert 2)
          ⁅Y,Z Rg z ⊓ Q Rg (alpha Rg)⁆ = ⊥ ∧ ⁅Y,Z Rg z⁆ ≤ Z Rg (alpha Rg) ∧
          ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
            let x := (embedM Rg r)⁻¹
            ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
              (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
              (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) =
                stabilizer Rg (alpha Rg) ∧
              edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) =
                stabilizer Rg (alpha Rg) ∧
              x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) :
                Set (FreeAmalgam Rg)) ∧
              Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
              ¬ ⁅Y,Z Rg (act Rg x z)⁆ ≤ Z Rg (alpha Rg))) :=
  (coreExhaustion_or_cubic_plane_pair_control h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
