module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.ImageCases.Basic

/-!
# The fixed quotient and its index-two intersection

A full natural section has moving quotient of order eight. Its fixed subgroup
modulo the radical has that same index, by the supplied direct decomposition.
The literal preimage B lies in this larger fixed subgroup: the residual acts
trivially modulo Z and Q acts trivially modulo the radical. Thus [V:B] ≥ 8.
Transport supplies this bound at the predecessor, and index multiplication
then gives the lower bound four in the small-image branch.

All quotient normality here is relative to the finite vertex stabilizer.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), p.884.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases

private theorem fixed_index_ge_eight {A : Type*} [Group A] [Finite A]
    {π : A →* SL} {Q L H N : Subgroup A}
    (s : SingleNaturalSection π Q L H N) (hgen : L ⊔ Q = ⊤) :
    letI := s.normal_kernel
    8 ≤ (centralizerModulo H L N).relIndex H := by
  let := s.normal_kernel
  let := s.normal_group
  let := s.radical_normal
  let D := radicalPreimage Q H N
  let q := QuotientGroup.mk' D
  let C := centralizerModulo H ⊤ D
  have htop : (⊤ : Subgroup A).map q = ⊤ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective D
  let : C.Normal := by
    change (H ⊓ (centralizer ((⊤ : Subgroup A).map q : Set (A ⧸ D))).comap q).Normal
    rw [htop]
    infer_instance
  have hBC : centralizerModulo H L N ≤ C := by
    intro x hx
    obtain ⟨hxH, hc⟩ := mem_centralizerModulo_iff.mp hx
    apply mem_centralizerModulo_iff.mpr
    refine ⟨hxH, ?_⟩
    have hcentral : (⊤ : Subgroup A).map q ≤ centralizer ({q x} : Set (A ⧸ D)) := by
      rw [← hgen, Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨l, hl, rfl⟩
        apply mem_centralizer_singleton_iff.mpr
        apply commutatorElement_eq_one_iff_mul_comm.mp
        rw [← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).mpr
          (show ⁅l, x⁆ ∈ D from (show N ≤ D from le_sup_left) (hc l hl))
      · rintro _ ⟨u, hu, rfl⟩
        apply mem_centralizer_singleton_iff.mpr
        apply commutatorElement_eq_one_iff_mul_comm.mp
        rw [← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).mpr
          (show ⁅u, x⁆ ∈ D from (show ⁅H, Q⁆ ≤ D from le_sup_right)
            (by rw [commutator_comm]; exact commutator_mem_commutator hu hxH))
    intro a ha
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅a, x⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mem_centralizer_singleton_iff.mp (hcentral (mem_map_of_mem q ha))
  have hindex : C.relIndex H = 8 := by
    calc
      C.relIndex H = C.relIndex (movingPreimage Q H N ⊔ C) :=
        congrArg (fun K => C.relIndex K) s.decomposition
      _ = C.relIndex (movingPreimage Q H N) := relIndex_sup_right _ _
      _ = (movingPreimage Q H N ⊓ C).relIndex (movingPreimage Q H N) :=
        (inf_relIndex_left _ _).symm
      _ = D.relIndex (movingPreimage Q H N) :=
        congrArg (fun K => K.relIndex (movingPreimage Q H N)) s.intersection
      _ = 8 := s.moving_quotient_card
  rw [← hindex]
  exact relIndex_le_of_le_left hBC index_ne_zero_of_finite


variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : MS93.Geometry R}

/-- The literal preimage B has index at least eight in V. The bound uses the
specified natural quotient and the actual residual-plus-kernel generation. -/
theorem fixed_quotient_ge_eight (source : LocalSource L R) (hb : 2 < geometry.b R)
    {a : Vertex R} (ha : color R a = false)
    (s : NaturalSectionAt a (V R a) (Z R a)) :
    8 ≤ (B R a (geometry.Z_normal a)).relIndex (V R a) := by
  let G := stabilizer R a
  let Q₀ := (Q R a).subgroupOf G
  let V₀ := (V R a).subgroupOf G
  let Z₀ := (Z R a).subgroupOf G
  let L₀ := pResidual 2 G
  let : Z₀.Normal := geometry.Z_normal a
  let := finite_stabilizer R a
  have hV : V R a ≤ G :=
    (geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)
  have hgen : L₀ ⊔ Q₀ = ⊤ := by
    apply Subgroup.map_injective (f := G.subtype) G.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le
      (show Q R a ≤ G from fun _ hx => hx.1)]
    change Ltilde R a ⊔ Q R a = (⊤ : Subgroup G).map G.subtype
    rw [source.local_generation a ha, ← MonoidHom.range_eq_map, range_subtype]
  have hi := fixed_index_ge_eight s.module_section hgen
  have heq := relIndex_map_map_of_injective
    (centralizerModulo V₀ L₀ Z₀) V₀ G.subtype_injective
  rw [map_subgroupOf_eq_of_le hV] at heq
  exact heq.symm ▸ hi


/-- The supplied initial facts yield a genuine natural section at any M-vertex.
No producer of InitialFacts or later escape conclusion is used. -/
theorem fixed_quotient_ge_eight_at (source : LocalSource L R)
    (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (a : Vertex R) (ha : color R a = false) :
    8 ≤ (B R a (geometry.Z_normal a)).relIndex (V R a) := by
  obtain ⟨q, hqa, _⟩ := contrary_at p bad a ha
  obtain ⟨iq⟩ := initial q
  have hs : NaturalSectionAt a (V R a) (Z R a) := by
    simpa only [hqa] using iq.natural_section
  exact fixed_quotient_ge_eight source hb ha hs

/-- The actual intersection quotient in the image-order-two case has order
at least four. Relative index retains the intersection with the denominator. -/
theorem small_intersection_quotient_ge_four (source : LocalSource L R)
    (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry)
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (hi : (Q R p.a).relIndex (V R p.c) = 2) :
    4 ≤ (V R p.c ⊓ B R p.c (geometry.Z_normal p.c)).relIndex
      (V R p.c ⊓ Q R p.a) :=
  intersection_index_ge_four hb p hi
    (fixed_quotient_ge_eight_at source hb initial p bad p.c p.before_color)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.ImageCases
