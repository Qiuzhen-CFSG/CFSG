module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.KernelAction
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank

/-!
# Paired secondary images with the central layers retained

The component and the actual common-edge kernel generate the local
stabilizer. The secondary seed commutator lies in the edge center and is
fixed by the component, hence by the full stabilizer. Normal generation
therefore gives the exact equality [A,Q] = [Y,Q], retaining its full central
subgroup.

This commutator bound puts the secondary Frattini image in the opposite
kernel. The marked opposite symplectic image is elementary abelian and has
order at most q cubed. Applying this at both endpoints bounds both images
and localizes the remaining paired commutator intersection in the common
edge center, fixed by both endpoint stabilizers.

Source: MS93 (3.6), printed p.871. The lower image bound, triviality of the
paired intersection, natural secondary section and final contradiction
still require proof; no center-free hypothesis or degree-two restriction
is used here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.CoreReconstruction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [Finite F] [CharP F 2] in
/-- The component and the literal edge kernel generate the endpoint stabilizer. -/
theorem replacement_edge_generation {a t : Vertex d.radical}
    (ha : color d.radical a = false) (hat : Adjacent d.radical a t) :
    Ltilde d.radical a ⊔ Q d.radical t = stabilizer d.radical a := by
  have hbase : Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (beta d.radical) =
      stabilizer d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,Q_beta,←Subgroup.map_sup,replacement_residual h d]
    have hsup : K.subgroupOf d.overgroup ⊔ d.radical = ⊤ := by
      apply top_unique
      intro x _
      obtain ⟨k,hk,r,hr,rfl⟩ := replacement_product h d x
      exact mul_mem_sup hk hr
    rw [hsup,←MonoidHom.range_eq_map]
    exact (stabilizer_m_base d.radical).symm
  obtain ⟨v,hv | hv⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · obtain ⟨rfl,rfl⟩ := hv
    have he₁ : act d.radical v (alpha d.radical) = mVertex d.radical v := by
      simp only [alpha,act_mVertex,one_mul]
    have he₂ : act d.radical v (beta d.radical) = hVertex d.radical v := by
      simp only [beta,act_hVertex,one_mul]
    have hh := congrArg (fun P => P.map (MulAut.conj v⁻¹).toMonoidHom) hbase
    rwa [Subgroup.map_sup,←Ltilde_act,←Q_act,←stabilizer_act,he₁,he₂] at hh
  · obtain ⟨rfl,rfl⟩ := hv
    simp [color,hVertex] at ha

/-- The secondary orbit retains exactly its seed commutator, which is fixed
by the entire local stabilizer and lies in the common edge center. -/
theorem replacement_secondary_commutator_eq_seed
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let Y := Sp4Four.secondarySeed d.radical a t z
    let A := Sp4Four.secondaryOrbit d.radical a Y
    ⁅A,Q d.radical a⁆ = ⁅Y,Q d.radical a⁆ ∧
      ⁅A,Q d.radical a⁆ ≤ Z d.radical t ⊓
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let Y := Sp4Four.secondarySeed d.radical a t z
  let A := Sp4Four.secondaryOrbit d.radical a Y
  let N := ⁅Y,Q d.radical a⁆
  have hYA : Y ≤ A := by
    change Y ≤ conjugatesIn Y (stabilizer d.radical a)
    rw [Sp4Four.conjugatesIn_eq_conjugateSpan]
    exact le_conjugateSpanBy _ _
  have hNA : N ≤ ⁅A,Q d.radical a⁆ := commutator_mono hYA le_rfl
  have hNt : N ≤ Z d.radical t :=
    (Sp4Four.secondarySeed_greatest d.radical g path.end_color hzt (by omega)).2.1
  have hNL : N ≤ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :=
    hNA.trans ((replacement_secondary_orbit_fixed_bounds h d path hb hat hzt hlarge).1.trans
      inf_le_right)
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  have hNQt : N ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro x hx
    have hh := hNt hx
    change x ∈ Z d.radical t at hh
    simp only [Z,ht,Bool.true_eq_false,↓reduceIte] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  have hNS : N ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←replacement_edge_generation h d path.start_color hat]
    exact sup_le (le_centralizer_iff.mp hNL) (le_centralizer_iff.mp hNQt)
  have hSN : stabilizer d.radical a ≤ normalizer N :=
    (le_centralizer_iff.mp hNS).trans (Subgroup.centralizer_le_normalizer _)
  have hAQ : ⁅A,Q d.radical a⁆ ≤ N :=
    conjugatesIn_commutator_le Y (stabilizer d.radical a) (Q d.radical a) N
      (replacement_secondary_seed_le_kernel h d path hb hat hzt hlarge)
      (Q_normalized d.radical a) hSN ((show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1).trans hSN) le_rfl
  exact ⟨le_antisymm hAQ hNA,le_inf (hAQ.trans hNt) (hAQ.trans hNS)⟩


open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative

/-- The actual opposite-kernel image of the secondary orbit is elementary,
has the literal intersection kernel, and has order at most q cubed. -/
theorem replacement_secondary_image
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    ∃ E : ChapterB.QuasisimpleSource.BinaryField, E.degree = n ∧
      ∃ f : A →* Sp E.Carrier,
        f.ker.map A.subtype = A ⊓ Q d.radical z ∧
        IsElementaryAbelian 2 f.range ∧
        Nat.card f.range = (Q d.radical z).relIndex A ∧
        Nat.card f.range ≤ (2^n)^3 := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  obtain ⟨hAQ,_,_⟩ := replacement_secondary_orbit_bounds h d path hb hat hzt hlarge
  obtain ⟨E,hE,f,hf,_⟩ := replacement_nonfrattini_kernel_root_action h d path hb hlarge
  let β : A →* Sp E.Carrier := f.comp (inclusion hAQ)
  have hbk (u : A) : u ∈ β.ker ↔ (u : FreeAmalgam d.radical) ∈ Q d.radical z := by
    constructor
    · intro hu
      exact (hf ▸ mem_map_of_mem (Q d.radical a).subtype
        (show inclusion hAQ u ∈ f.ker from hu)).2
    · intro hu
      have hh : (u : FreeAmalgam d.radical) ∈ f.ker.map (Q d.radical a).subtype :=
        hf.symm ▸ ⟨hAQ u.property,hu⟩
      obtain ⟨x,hx,hxv⟩ := hh
      have he : x = inclusion hAQ u := Subtype.ext hxv
      change f (inclusion hAQ u) = 1
      change f x = 1 at hx
      rwa [he] at hx
  have hbkmap : β.ker.map A.subtype = A ⊓ Q d.radical z := by
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property,(hbk u).mp hu⟩
    · rintro ⟨ha,hz⟩
      exact ⟨⟨x,ha⟩,(hbk ⟨x,ha⟩).mpr hz,rfl⟩
  have hphiz : (frattini A).map A.subtype ≤ Q d.radical z := by
    have ht := (replacement_secondary_commutator_eq_seed h d path hb hat hzt hlarge).2
    have hseed := Sp4Four.secondary_orbit_frattini_le d.radical g
      (replacement_isPGroup h d) (replacement_core_le h d)
      path.start_color path.end_color (by omega)
      (Sp4Four.secondarySeed d.radical a t z)
      (Sp4Four.secondarySeed_le d.radical a t z)
      (replacement_secondary_seed_le_kernel h d path hb hat hzt hlarge)
    exact hseed.trans (ht.trans (inf_le_left.trans
      ((Sp4Four.edge_Z_le_endpoint d.radical path.end_color hzt).trans
        ((g.omega_bound z path.end_color (by
          rw [g.distance_constant z path.end_color]
          change 0 < g.b d.radical
          omega)).trans (omegaCenter_le _)))))
  let : Finite (stabilizer d.radical a) := finite_stabilizer d.radical a
  let : Finite A := Finite.of_injective
    (inclusion (hAQ.trans (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1)))
    (inclusion_injective _)
  let : Fact (IsPGroup 2 A) := ⟨(Q_isPGroup d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) a path.start_color).of_injective
      (inclusion hAQ) (inclusion_injective _)⟩
  have hpow (u : A) : β u ^ 2 = 1 := by
    rw [←map_pow]
    exact (hbk (u^2)).mpr (hphiz (mem_map_of_mem A.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) u)))
  have hpow' (u : β.range) : u^2=1 := by
    obtain ⟨x,hx⟩ := u.property
    apply Subtype.ext
    change u.val^2=1
    rw [←hx]
    exact hpow x
  let : IsElementaryAbelian 2 β.range := {
    toIsMulCommutative := by
      refine ⟨⟨fun x y => ?_⟩⟩
      have hinv (x : β.range) : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hpow' x)
      calc
        x*y = (x*y)⁻¹ := (hinv _).symm
        _ = y*x := by rw [mul_inv_rev,hinv,hinv]
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow' }
  have hidx : Nat.card β.range = (Q d.radical z).relIndex A := by
    have hh := CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison.quotient_image_card
      A (Q d.radical a) (Q d.radical a ⊓ Q d.radical z) hAQ f hf
    change Nat.card β.range = _ at hh
    rw [hh]
    change ((Q d.radical a ⊓ Q d.radical z).subgroupOf A).index =
      ((Q d.radical z).subgroupOf A).index
    congr 1
    ext u
    exact ⟨fun hu => hu.2,fun hu => ⟨hAQ u.property,hu⟩⟩
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  obtain ⟨S,hS⟩ := (IsElementaryAbelian.isPGroup 2 β.range).exists_le_sylow
  obtain ⟨v,hv⟩ := MulAction.exists_smul_eq (Sp E.Carrier) S
    (unipotentSylow hFc (lt_trans Nat.zero_lt_one h.nonbinary))
  have hSm : (S : Subgroup (Sp E.Carrier)).map (MulAut.conj v).toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hv
  let B := β.range.map (MulAut.conj v).toMonoidHom
  have hBU : B ≤ unipotent := hSm ▸ map_mono hS
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (B.subgroupOf unipotent) := IsElementaryAbelian.subgroupOf hBU
  have hcard : Nat.card β.range = Nat.card (B.subgroupOf unipotent) :=
    (Nat.card_congr (β.range.equivMapOfInjective _ (MulAut.conj v).injective).toEquiv).trans
      (Nat.card_congr (subgroupOfEquivOfLe hBU).toEquiv).symm
  refine ⟨E,hE,β,hbkmap,inferInstance,hidx,?_⟩
  rw [hcard,←hFc]
  exact EvenTwoRank.elementary_card_le _


/-- The two actual secondary orbits have image order at most q cubed. Their
Frattini images are controlled by their respective seed commutators, and the
remaining intersection is central in both endpoint stabilizers. -/
theorem replacement_paired_secondary_bounds
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    let Y := Sp4Four.secondarySeed d.radical a t z
    let Y' := Sp4Four.secondarySeed d.radical z t a
    let A := Sp4Four.secondaryOrbit d.radical a Y
    let A' := Sp4Four.secondaryOrbit d.radical z Y'
    (Q d.radical z).relIndex A ≤ (2^n)^3 ∧
      (Q d.radical a).relIndex A' ≤ (2^n)^3 ∧
      (frattini A).map A.subtype ≤ ⁅Y,Q d.radical a⁆ ∧
      (frattini A').map A'.subtype ≤ ⁅Y',Q d.radical z⁆ ∧
      ⁅Y,Q d.radical a⁆ ⊓ ⁅Y',Q d.radical z⁆ ≤
        Z d.radical t ⊓ centralizer
          ((stabilizer d.radical a ⊔ stabilizer d.radical z :
            Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  have hpos : 0 < g.b d.radical := by omega
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; exact hpos)
        z path.end_color path.critical }
  have hlarge' : ¬ core d.radical z ≤
      (frattini (Q d.radical z)).map (Q d.radical z).subtype ⊔ X d.radical z := by
    obtain ⟨v,hv⟩ := exists_mVertex_of_color d.radical path.start_color
    have he : act d.radical v (alpha d.radical) = a := by
      rw [hv]
      simp only [alpha,act_mVertex,one_mul]
    have hbase := (nonfrattini_act_iff d.radical v (alpha d.radical)).mp
      (he.symm ▸ hlarge)
    exact nonfrattini_at_vertex d.radical hbase path.end_color
  obtain ⟨_,_,_,_,_,hcard,hbound⟩ := replacement_secondary_image h d path hb hat hzt hlarge
  obtain ⟨_,_,_,_,_,hcard',hbound'⟩ := replacement_secondary_image h d rev hb hzt hat hlarge'
  obtain ⟨he,hcentral⟩ := replacement_secondary_commutator_eq_seed h d path hb hat hzt hlarge
  obtain ⟨he',hcentral'⟩ := replacement_secondary_commutator_eq_seed h d rev hb hzt hat hlarge'
  rw [he] at hcentral
  rw [he'] at hcentral'
  have hphi := Sp4Four.secondary_orbit_frattini_le d.radical g
    (replacement_isPGroup h d) (replacement_core_le h d)
    path.start_color path.end_color hpos (Sp4Four.secondarySeed d.radical a t z)
    (Sp4Four.secondarySeed_le d.radical a t z)
    (replacement_secondary_seed_le_kernel h d path hb hat hzt hlarge)
  have hphi' := Sp4Four.secondary_orbit_frattini_le d.radical g
    (replacement_isPGroup h d) (replacement_core_le h d)
    path.end_color path.start_color hpos (Sp4Four.secondarySeed d.radical z t a)
    (Sp4Four.secondarySeed_le d.radical z t a)
    (replacement_secondary_seed_le_kernel h d rev hb hzt hat hlarge')
  rw [he] at hphi
  rw [he'] at hphi'
  refine ⟨hcard ▸ hbound,hcard' ▸ hbound',hphi,hphi',?_⟩
  refine le_inf (inf_le_left.trans (hcentral.trans inf_le_left)) ?_
  apply le_centralizer_iff.mp
  exact sup_le
    (le_centralizer_iff.mp (inf_le_left.trans (hcentral.trans inf_le_right)))
    (le_centralizer_iff.mp (inf_le_right.trans (hcentral'.trans inf_le_right)))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
