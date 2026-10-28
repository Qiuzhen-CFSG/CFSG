module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Generation

/-!
# Coordinates on a full single natural section

Residual commutator idempotence identifies the fixed preimage modulo N
with the fixed summand modulo N[H,Q]. The natural moving coordinates extend
across that summand and then descend through a surjective ambient map whose
kernel meets H in the fixed part. Both constructions preserve the marking,
the intrinsic kernel, and the actual conjugation equation.

The extension construction is adapted from the generic
`DistanceFour.Flags.RankOne.Propagation.Pairing.extendNaturalAcrossFixed`;
no later escape or distance-four conclusion is used.
Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)(iii), pp.882--883,
and the first quotient application in (4.3.2)(2), printed p.883.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.NaturalGeneration
open RankOnePairing

/-- Extend moving coordinates across a normal summand on which they vanish.
The intersection is the exact intrinsic kernel, and the extended map retains
the original marking and the action of every ambient element. -/
noncomputable def extendNaturalAcrossFixed {G : Type*} [Group G] {π : G →* SL}
    {A H N C : Subgroup G} [C.Normal]
    (n : NaturalFactor π ⊤ A N) (hcover : H = A ⊔ C)
    (hinter : A ⊓ C = N) (hH : (⊤ : Subgroup G) ≤ normalizer H) :
    NaturalFactor π ⊤ H C := by
  have hAH : A ≤ H := hcover ▸ le_sup_left
  have hCH : C ≤ H := hcover ▸ le_sup_right
  have factor (x : H) : ∃ a : A, ∃ c : C, (a : G) * (c : G) = x := by
    obtain ⟨a, ha, c, hc, he⟩ := mem_sup_of_normal_right.mp (show (x : G) ∈ A ⊔ C from by rw [← hcover]; exact x.property)
    exact ⟨⟨a, ha⟩, ⟨c, hc⟩, he⟩
  let q := QuotientGroup.mk' (C.subgroupOf H)
  let f := q.comp (inclusion hAH)
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf H) v
    obtain ⟨a, c, he⟩ := factor x
    refine ⟨a, ?_⟩
    change q (inclusion hAH a) = q x
    have he' : inclusion hAH a * inclusion hCH c = x := Subtype.ext he
    have hc : q (inclusion hCH c) = 1 := (QuotientGroup.eq_one_iff _).mpr c.property
    rw [← he', map_mul, hc, mul_one]
  have hk : f.ker ≤ n.coordinates.ker := by
    intro a ha
    rw [n.kernel]
    have hc : inclusion hAH a ∈ C.subgroupOf H := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact ha
    change (a : G) ∈ N
    rw [← hinter]
    exact ⟨a.property, hc⟩
  let F := f.liftOfSurjective hf ⟨n.coordinates, hk⟩
  let coordinates := F.comp q
  have hA (a : A) : coordinates (inclusion hAH a) = n.coordinates a :=
    MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨n.coordinates, hk⟩ a
  have hC (c : C) : coordinates (inclusion hCH c) = 1 := by
    change F (q (inclusion hCH c)) = 1
    rw [show q (inclusion hCH c) = 1 from (QuotientGroup.eq_one_iff _).mpr c.property,
      map_one]
  have hproduct (x : H) (a : A) (c : C) (he : (a : G) * (c : G) = x) :
      coordinates x = n.coordinates a := by
    have he' : inclusion hAH a * inclusion hCH c = x := Subtype.ext he
    rw [← he', map_mul, hA, hC, mul_one]
  refine {
    marking := n.marking
    coordinates := coordinates
    surjective := ?_
    kernel := ?_
    normalized := hH
    action := ?_ }
  · intro v
    obtain ⟨a, ha⟩ := n.surjective v
    exact ⟨inclusion hAH a, (hA a).trans ha⟩
  · ext x
    change coordinates x = 1 ↔ (x : G) ∈ C
    obtain ⟨a, c, he⟩ := factor x
    rw [hproduct x a c he, ← MonoidHom.mem_ker, n.kernel]
    change (a : G) ∈ N ↔ (x : G) ∈ C
    constructor
    · intro ha
      rw [← hinter] at ha
      rw [← he]
      exact C.mul_mem ha.2 c.property
    · intro hx
      have ha : (a : G) ∈ C := by
        have hh := C.mul_mem hx (C.inv_mem c.property)
        rwa [← he, mul_inv_cancel_right] at hh
      rw [← hinter]
      exact ⟨a.property, ha⟩
  · intro l hl x y hy
    obtain ⟨a, c, he⟩ := factor x
    let a' : A := ⟨l * (a : G) * l⁻¹,
      (mem_normalizer_iff.mp (n.normalized hl) _).mp a.property⟩
    let c' : C := ⟨l * (c : G) * l⁻¹, (inferInstance : C.Normal).conj_mem _ c.property l⟩
    have he' : (a' : G) * (c' : G) = y := by
      change (l * (a : G) * l⁻¹) * (l * (c : G) * l⁻¹) = (y : G)
      rw [hy, ← he]
      group
    change (coordinates y).toAdd = _
    rw [hproduct y a' c' he', hproduct x a c he]
    exact n.action l hl a a' rfl


@[simp] theorem extendNaturalAcrossFixed_marking {G : Type*} [Group G] {π : G →* SL}
    {A H N C : Subgroup G} [C.Normal]
    (n : NaturalFactor π ⊤ A N) (hcover : H = A ⊔ C)
    (hinter : A ⊓ C = N) (hH : (⊤ : Subgroup G) ≤ normalizer H) :
    (extendNaturalAcrossFixed n hcover hinter hH).marking = n.marking := rfl

private theorem commutator_sup_bound {G : Type*} [Group G]
    {A B K N : Subgroup G} [N.Normal]
    (hA : ⁅A, K⁆ ≤ N) (hB : ⁅B, K⁆ ≤ N) : ⁅A ⊔ B, K⁆ ≤ N := by
  have h : A ⊔ B ≤ commutatorPreimage ⊤ K N :=
    sup_le (le_commutatorPreimage le_top hA) (le_commutatorPreimage le_top hB)
  exact (commutator_mono h le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)

/-- Coprime commutator idempotence identifies the literal fixed preimage
modulo N with the full fixed part modulo N[H,Q]. -/
theorem fixed_eq_radical_fixed {G : Type*} [Group G] [Finite G]
    {π : G →* SL} {Q L H N : Subgroup G}
    (s : SingleNaturalSection π Q L H N)
    (hL : IsPPerfect 2 L) (hH : IsPGroup 2 H) (hgen : L ⊔ Q = ⊤) :
    letI := s.normal_kernel
    letI := s.radical_normal
    centralizerModulo H L N = centralizerModulo H ⊤ (radicalPreimage Q H N) := by
  let := s.normal_kernel
  let := s.normal_group
  let := s.radical_normal
  let D := radicalPreimage Q H N
  let C := centralizerModulo H ⊤ D
  let : C.Normal := by
    change (H ⊓ (centralizer ((⊤ : Subgroup G).map
      (QuotientGroup.mk' D) : Set (G ⧸ D))).comap (QuotientGroup.mk' D)).Normal
    rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    infer_instance
  have hDL : ⁅D, L⁆ ≤ N :=
    commutator_sup_bound (commutator_le_left _ _) s.triple_le
  apply le_antisymm
  · intro x hx
    obtain ⟨hxH, hxL⟩ := mem_centralizerModulo_iff.mp hx
    apply mem_centralizerModulo_iff.mpr
    refine ⟨hxH, ?_⟩
    let q := QuotientGroup.mk' D
    have hcentral : (⊤ : Subgroup G).map q ≤ centralizer ({q x} : Set (G ⧸ D)) := by
      rw [← hgen, Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨l, hl, rfl⟩
        apply mem_centralizer_singleton_iff.mpr
        apply commutatorElement_eq_one_iff_mul_comm.mp
        rw [← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).mpr
          (show ⁅l, x⁆ ∈ D from (show N ≤ D from le_sup_left) (hxL l hl))
      · rintro _ ⟨u, hu, rfl⟩
        apply mem_centralizer_singleton_iff.mpr
        apply commutatorElement_eq_one_iff_mul_comm.mp
        rw [← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).mpr
          (show ⁅u, x⁆ ∈ D from (show ⁅H, Q⁆ ≤ D from le_sup_right)
            (by rw [commutator_comm]; exact commutator_mem_commutator hu hxH))
    intro g hg
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅g, x⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mem_centralizer_singleton_iff.mp (hcentral (mem_map_of_mem q hg))
  · have hCL : ⁅C, L⁆ ≤ D := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro l _ x hx
      exact (mem_centralizerModulo_iff.mp hx).2 l (mem_top _)
    have hCN : ⁅C, L⁆ ≤ N := by
      rw [← commutator_isPPerfect_idempotent L C hL
        (hH.to_le (centralizerModulo_le _ _ _)) le_normalizer_of_normal]
      exact (commutator_mono hCL le_rfl).trans hDL
    intro x hx
    exact mem_centralizerModulo_iff.mpr ⟨(mem_centralizerModulo_iff.mp hx).1,
      fun l hl => (commutator_comm C L ▸ hCN) (commutator_mem_commutator hl hx)⟩


/-- Coordinates on the whole section, modulo its literal residual-fixed part. -/
noncomputable def sectionCoordinates {G : Type*} [Group G] [Finite G]
    {π : G →* SL} {Q L H N : Subgroup G}
    (s : SingleNaturalSection π Q L H N)
    (hL : IsPPerfect 2 L) (hH : IsPGroup 2 H) (hgen : L ⊔ Q = ⊤) :
    letI := s.normal_kernel
    NaturalFactor π ⊤ H (centralizerModulo H L N) := by
  let := s.normal_kernel
  let := s.normal_group
  let := s.radical_normal
  let C := centralizerModulo H ⊤ (radicalPreimage Q H N)
  let : C.Normal := by
    change (H ⊓ (centralizer ((⊤ : Subgroup G).map
      (QuotientGroup.mk' (radicalPreimage Q H N)) : Set _)).comap
        (QuotientGroup.mk' (radicalPreimage Q H N))).Normal
    rw [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    infer_instance
  let n := extendNaturalAcrossFixed s.natural s.decomposition s.intersection
    le_normalizer_of_normal
  exact { n with kernel := by rw [fixed_eq_radical_fixed s hL hH hgen]; exact n.kernel }

@[simp] theorem sectionCoordinates_marking {G : Type*} [Group G] [Finite G]
    {π : G →* SL} {Q L H N : Subgroup G}
    (s : SingleNaturalSection π Q L H N)
    (hL : IsPPerfect 2 L) (hH : IsPGroup 2 H) (hgen : L ⊔ Q = ⊤) :
    (sectionCoordinates s hL hH hgen).marking = s.natural.marking := rfl

/-- Descent of genuine natural coordinates through a surjective ambient map.
The image kernel is proved from the original intrinsic kernel. -/
noncomputable def mapNaturalFactor {G G' : Type*} [Group G] [Group G']
    {π : G →* SL} {π' : G' →* SL} {H N : Subgroup G}
    (n : NaturalFactor π ⊤ H N) (q : G →* G') (hq : Function.Surjective q)
    (hπ : π'.comp q = π) (hNH : N ≤ H) (hker : H ⊓ q.ker ≤ N) :
    NaturalFactor π' ⊤ (H.map q) (N.map q) := by
  let f := q.subgroupMap H
  have hf : Function.Surjective f := q.subgroupMap_surjective H
  have hk : f.ker ≤ n.coordinates.ker := by
    intro x hx
    rw [n.kernel]
    exact hker ⟨x.property, congrArg Subtype.val hx⟩
  let c := f.liftOfSurjective hf ⟨n.coordinates, hk⟩
  have hc (x : H) : c (f x) = n.coordinates x :=
    MonoidHom.liftOfRightInverse_comp_apply f (Function.surjInv hf)
      (Function.rightInverse_surjInv hf) ⟨n.coordinates, hk⟩ x
  refine {
    marking := n.marking
    coordinates := c
    surjective := ?_
    kernel := ?_
    normalized := ?_
    action := ?_ }
  · intro v
    obtain ⟨x, hx⟩ := n.surjective v
    exact ⟨f x, (hc x).trans hx⟩
  · ext x'
    obtain ⟨x, rfl⟩ := hf x'
    change c (f x) = 1 ↔ q (x : G) ∈ N.map q
    rw [hc, ← MonoidHom.mem_ker, n.kernel]
    change (x : G) ∈ N ↔ q (x : G) ∈ N.map q
    constructor
    · exact mem_map_of_mem q
    · rintro ⟨y, hy, he⟩
      have hxy : (x : G) * y⁻¹ ∈ H ⊓ q.ker := by
        refine ⟨H.mul_mem x.property (H.inv_mem (hNH hy)), ?_⟩
        change q ((x : G) * y⁻¹) = 1
        rw [map_mul, map_inv, he, mul_inv_cancel]
      have hh := N.mul_mem (hker hxy) hy
      simpa only [inv_mul_cancel_right] using hh
  · let : H.Normal := ⟨fun x hx g =>
      (mem_normalizer_iff.mp (n.normalized (mem_top g)) x).mp hx⟩
    let : (H.map q).Normal := Normal.map inferInstance q hq
    exact le_normalizer_of_normal
  · intro l' _ x' y' hy
    obtain ⟨l, rfl⟩ := hq l'
    obtain ⟨x, rfl⟩ := hf x'
    let y : H := ⟨l * (x : G) * l⁻¹,
      (mem_normalizer_iff.mp (n.normalized (mem_top _)) _).mp x.property⟩
    have he : f y = y' := by
      apply Subtype.ext
      change q (l * (x : G) * l⁻¹) = (y' : G')
      rw [map_mul, map_mul, map_inv]
      exact hy.symm
    change (c y').toAdd = _
    rw [← he, hc, hc]
    have hπl : π' (q l) = π l := congrArg (fun f : G →* SL => f l) hπ
    rw [hπl]
    exact n.action l (mem_top _) x y rfl

@[simp] theorem mapNaturalFactor_marking {G G' : Type*} [Group G] [Group G']
    {π : G →* SL} {π' : G' →* SL} {H N : Subgroup G}
    (n : NaturalFactor π ⊤ H N) (q : G →* G') (hq : Function.Surjective q)
    (hπ : π'.comp q = π) (hNH : N ≤ H) (hker : H ⊓ q.ker ≤ N) :
    (mapNaturalFactor n q hq hπ hNH hker).marking = n.marking := rfl

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.NaturalGeneration
