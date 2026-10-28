module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFiveCentralizer
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFiveCore
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFiveEquality

/-!
# Equality of the original full Z-layers in MS93 (3.7)(5)

For the field-sized critical image, source (3) already identifies X with Z.
For a larger critical image, the plane-radical centralizer of an element
has order q modulo the endpoint core and bounds its omega displacement.
The whole-core dual cover then puts every fixed involution in Z: the
order-q actor cannot preserve a quadratic refinement. Together with the
core comparison this proves equality of the two full original Z-layers.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(5), pp.875--876,
using the dual-cover argument (1.5)(ii). The three printed antecedents
are retained. Their construction in (6) remains a separate proof step.
-/

public noncomputable section
open Matrix Subgroup Theory.GroupTheory Representation Representation.OneCohomology Representation.BinaryOffender
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource
open SaturatedDistanceTwo (small_displacement_no_refinement)
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
include h hshort hinner

/-- The order-q and omega-displacement counts in source (5) force every
fixed involution into the actual generated Z-layer. -/
theorem original_source_five_fixed_omega_mem_Z
    (g : Geometry R) (hb : g.b R=2)
    {a t : Vertex R} (ha : color R a=false)
    (hat : Adjacent R a t)
    (B : Subgroup (FreeAmalgam R)) (hBT : B ≤ Q R t)
    (hcard : (Q R a).relIndex B=2^n)
    (hmove : (U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R))).relIndex
      ⁅X R a,B⁆ ≤ 2^n)
    (x : FreeAmalgam R) (hx : x ∈ X R a)
    (hfix : x ∈ centralizer (B : Set (FreeAmalgam R))) :
    x ∈ Z R a := by
  obtain ⟨E,hE,s,γ,_hγinj,hγ,_hL,i,hi,hd,hrange,_⟩ :=
    short_original_wholeKernel_natural_dualCover h hshort ha
  have hCtop : K.map (QuotientGroup.mk' (pCore 2 H))=⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q=⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  have hγonto : Function.Surjective γ := MonoidHom.range_eq_top.mp (hγ.trans hCtop)
  have hγinj : Function.Injective γ := by
    intro a b hab
    apply binaryNatural_injective
    apply LinearMap.ext
    intro v
    apply hi
    rw [i.isIntertwining,i.isIntertwining]
    change s.action (γ a) (i v)=s.action (γ b) (i v)
    rw [hab]
  let e := MulEquiv.ofBijective γ ⟨hγinj,hγonto⟩
  have hBS := hBT.trans (original_edge_le_stabilizer R hat)
  let β := e.symm.toMonoidHom.comp (s.quotient.comp (inclusion hBS))
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hβ (b : B) : γ (β b)=s.quotient (inclusion hBS b) := e.apply_symm_apply _
  have hk : α.ker=(Q R a).subgroupOf B := by
    dsimp only [α,β]
    rw [MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective,
      MonoidHom.ker_comp_of_injective _ _ e.symm.injective,←MonoidHom.comap_ker]
    have hs : s.quotient.ker=(Q R a).subgroupOf (stabilizer R a) := by
      rw [←s.quotient_kernel,subgroupOf_map_subtype_eq]
    rw [hs,comap_inclusion_subgroupOf]
  have hEc : Nat.card E.Carrier=2^n := E.card_eq.trans (congrArg (2^·) hE)
  have hc : Nat.card α.range=Nat.card E.Carrier := by
    rw [←index_ker,hk,hEc]
    exact hcard
  let π := s.sectionData.coordinates
  let N := ⁅X R a,B⁆
  have hXQ : X R a ≤ Q R a := omegaCenter_le _
  have hUX : U R a ≤ X R a := (U_le_Z a).trans
    (g.omega_bound a ha (by rw [g.distance_constant a ha]; change 0<g.b R; omega))
  have hNQ : N ≤ Q R a := by
    dsimp only [N]
    rw [commutator_comm]
    exact (commutator_mono le_rfl hXQ).trans
      (le_normalizer_iff_commutator_le_right.mp (hBS.trans (Q_normalized R a)))
  let N₀ := (N.subgroupOf (Q R a)).map π
  have hNc : Nat.card N₀ ≤ Nat.card E.Carrier := by
    have he : Nat.card N₀=(fixedCore R a).relIndex N := by
      rw [←relIndex_ker,s.sectionData.kernel_eq,relIndex_subgroupOf hNQ]
      rfl
    rw [he,hEc]
    apply le_trans ?_ hmove
    let := finite_stabilizer R a
    let : Finite N := Finite.of_injective
      (inclusion (hNQ.trans (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)))
      (inclusion_injective _)
    apply relIndex_le_of_le_left ?_ index_ne_zero_of_finite
    exact inf_le_inf (hUX.trans hXQ) le_rfl
  have hgen (b : B) (v : Vector E.Carrier) :
      Multiplicative.ofAdd (i (α b • v-v)) ∈ N₀ := by
    obtain ⟨u,hu,heu⟩ := (hrange (i v)).mp ⟨v,rfl⟩
    let w : Q R a :=
      ⟨b.val*u.val*b.val⁻¹,
        (mem_normalizer_iff.mp (Q_normalized R a (hBS b.property)) u).mp u.property⟩*u⁻¹
    refine ⟨w,?_,?_⟩
    · change ⁅b.val,u.val⁆ ∈ ⁅X R a,B⁆
      rw [commutator_comm]
      exact commutator_mem_commutator b.property (hUX hu)
    · apply Multiplicative.toAdd.injective
      change (π w).toAdd=i (α b • v-v)
      dsimp only [w,π]
      rw [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg]
      have heq := s.sectionData.equivariant (inclusion hBS b) u
      change (s.sectionData.coordinates ⟨b.val*u.val*b.val⁻¹,_⟩).toAdd=
        s.action (s.quotient (inclusion hBS b)) (s.sectionData.coordinates u).toAdd at heq
      rw [heq,heu,map_sub]
      change s.action (s.quotient (inclusion hBS b)) (i v)-i v=
        i (binaryNatural (β b) v)-i v
      rw [i.isIntertwining]
      change s.action (s.quotient (inclusion hBS b)) (i v)-i v=
        s.action (γ (β b)) (i v)-i v
      rw [hβ]
  have hD (v : Vector E.Carrier) (hv : v ∈ displacementSpace α.range) :
      Multiplicative.ofAdd (i v) ∈ N₀ := by
    have hs : ∀ k : E.Carrier, Multiplicative.ofAdd (i (k • v)) ∈ N₀ := by
      induction hv using Submodule.span_induction with
      | mem v hv =>
        rcases hv with ⟨⟨b,w⟩,rfl⟩
        obtain ⟨a,ha⟩ := b.property
        intro k
        change Multiplicative.ofAdd (i (k • (b.val • w-w))) ∈ N₀
        rw [←ha]
        simpa only [smul_sub,smul_comm (α a) k] using hgen a (k • w)
      | zero => intro k; simp
      | add v w hv hw ihv ihw =>
        intro k
        simpa only [smul_add,map_add,ofAdd_add] using N₀.mul_mem (ihv k) (ihw k)
      | smul k v hv ih => intro l; simpa only [smul_smul] using ih (l*k)
    simpa only [one_smul] using hs 1
  have hDc : Nat.card (displacementSpace α.range) ≤ Nat.card E.Carrier := by
    let f : displacementSpace α.range → N₀ := fun v => ⟨Multiplicative.ofAdd (i v),hD v v.property⟩
    have hf : Function.Injective f := by
      intro v w he
      exact Subtype.ext (hi (Multiplicative.ofAdd.injective (congrArg Subtype.val he)))
    exact (Nat.card_le_card_of_injective f hf).trans hNc
  have hElarge : 2<Nat.card E.Carrier := by
    rw [hEc]
    exact Nat.pow_lt_pow_right (by decide : 1 < (2:ℕ)) h.nonbinary
  have hno := small_displacement_no_refinement hElarge α.range hc hDc
  have hno' : ¬ ∃ v : Natural (K := E.Carrier), ∀ b : β.range, ∀ w,
      Plane.OrthogonalActors.refinement v (binaryNatural b.val w)=Plane.OrthogonalActors.refinement v w := by
    rintro ⟨v,hv⟩
    apply hno
    refine ⟨v,?_⟩
    rintro ⟨b,⟨y,rfl⟩⟩ w
    exact hv ⟨β y,⟨y,rfl⟩⟩ w
  let xQ : Q R a := ⟨x,hXQ hx⟩
  have hfixed : (π xQ).toAdd ∈ OneCohomology.fixed ((s.action.comp γ).comp β.range.subtype) := by
    rintro ⟨b,⟨y,rfl⟩⟩
    change s.action (γ (β y)) (π xQ).toAdd=_
    rw [hβ]
    have heq := s.sectionData.equivariant (inclusion hBS y) xQ
    change (π ⟨y.val*x*y.val⁻¹,_⟩).toAdd=
      s.action (s.quotient (inclusion hBS y)) (π xQ).toAdd at heq
    rw [←heq]
    congr 2
    apply Subtype.ext
    change y.val*x*y.val⁻¹=x
    rw [hfix y.val y.property,mul_inv_cancel_right]
  have hmem := dualCover_fixed_le_natural_of_no_refinement i hi hd β.range hno' hfixed
  obtain ⟨u,hu,heu⟩ := (hrange _).mp hmem
  have hdu : (u⁻¹*xQ : Q R a) ∈ π.ker := by
    change π (u⁻¹*xQ)=1
    rw [map_mul,map_inv,Multiplicative.toAdd.injective heu,inv_mul_cancel]
  rw [s.sectionData.kernel_eq] at hdu
  have hdX : u.val⁻¹*x ∈ X R a :=
    (X R a).mul_mem ((X R a).inv_mem (hUX hu)) hx
  have hdZ := original_fixed_X_le_edge h hinner ha hat ⟨hdX,hdu.2⟩
  have hh := (Z R a).mul_mem (U_le_Z a hu)
    (Sp4Four.edge_Z_le_endpoint R ha hat hdZ)
  simpa only [mul_inv_cancel_left] using hh


variable (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include hnsyl

/-- MS93 (3.7)(5), with the same midpoint and all three printed antecedents.
The centralizer count handles the plane branch; source (3) handles the
field-sized branch. -/
theorem original_source_five_Z_equality
    (g : Geometry R) (hb : g.b R=2)
    {a z t v : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hvt : Adjacent R v t) (hv : color R v=false)
    (hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) =
      U R v ⊓ centralizer (Ltilde R v : Set (FreeAmalgam R)))
    (hmove : ⁅Z R v,Q R t⁆=⁅Z R a,Q R t⁆)
    (hinside : Z R v ≤ Q R a) :
    Z R v=Z R a := by
  obtain ⟨hQ,hX⟩ := original_source_five_core_equality h hshort hinner path.start_color hv hat hvt hfixed hmove hinside
  have hcard : Nat.card (Z R a)=Nat.card (Z R v) := by
    obtain ⟨u,_,he⟩ := stabilizer_transitive_neighbors R t
      (adjacent_symm R hat) (adjacent_symm R hvt)
    rw [←he,Z_act,card_map_of_injective (MulAut.conj u⁻¹).injective]
  let := finite_Z R a
  let := finite_Z R v
  by_cases hlarge : (2^n)^2 ≤ (Q R z).relIndex (Z R a)
  · apply (Subgroup.eq_of_le_of_card_ge (K := Z R v) ?_ hcard.ge).symm
    intro x hx
    by_cases hxt : x ∈ Z R t
    · exact Sp4Four.edge_Z_le_endpoint R hv hvt hxt
    have hc := original_source_five_large_omega_displacement h hshort hinner hnsyl g hb path hat hzt hlarge x hx hxt
    let B := Q R t ⊓ centralizer ({x} : Set (FreeAmalgam R))
    apply original_source_five_fixed_omega_mem_Z h hshort hinner g hb hv hvt B inf_le_left
      (by rw [←hQ]; exact hc.1) (by rw [←hfixed,←hX]; exact hc.2.le) x
      (hX ▸ g.omega_bound a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0<g.b R; omega) hx)
    intro b hb
    exact mem_centralizer_singleton_iff.mp hb.2
  · have hsmall : (Q R z).relIndex (Z R a)=2^n := by
      simpa only [h.field_card] using
        (h.original_small_critical_indices_eq_field path (by omega)
          (by simpa only [h.field_card] using lt_of_not_ge hlarge)).1
    have he := (original_source_three_of_field_critical h hshort hinner hnsyl g hb path hat hzt hsmall).2.2.1
    apply Subgroup.eq_of_le_of_card_ge ?_ hcard.le
    rw [←he,hX]
    exact g.omega_bound v hv (by rw [g.distance_constant v hv]; change 0<g.b R; omega)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
