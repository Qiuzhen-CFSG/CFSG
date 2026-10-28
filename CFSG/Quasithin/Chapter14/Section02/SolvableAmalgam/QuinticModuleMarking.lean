module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.IndexFiveStructure
public import Theory.Representation.BinaryFiveOrbitMarking


/-!
# Marking the original quintic quotient module

The original invariant flag identifies the quotient point with Ω₁Z(T)
and its H-span with the literal conjugate span of the original plane.
The unique nonzero image of that plane is Sylow-fixed and its H-orbit spans
the tilded module. The original action kernel is O₂(H), so an element of
order five forces degree at least four. The five-orbit kernel calculation
then gives a full or deleted permutation-space marking, preserving that
same generator and each original orbit vector.

This supplies actual module coordinates to the asymmetric amalgam argument;
it does not assert a Ree/Tits endpoint or amalgam identification.

Source: Aschbacher--Smith14.2.6,14.2.20--21 and14.6.12(2),
printed pp.982,988--989 and1031.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 Chapter15.Section03.InitialSource
  ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem tilde_seed_orbit {T : Sylow 2 G} {V : Subgroup G}
    [IsElementaryAbelian 2 V] (F : InvariantFlag T V 2) (H : Subgroup G)
    (hHF : H ≤ F.H) (hTH : (T : Subgroup G) ≤ H)
    (hVN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hV : Nat.card V = 4) [IsElementaryAbelian 2 (F.tilde (F.UH H))] :
    ∃ w : F.tilde (F.UH H), w ≠ 1 ∧
      (∀ s : T.subtype hTH,
        F.localTildeAction H hHF s w = w) ∧
      Submodule.span (ZMod 2) (Set.range (fun h : H =>
        Representation.elementaryRepresentation (p := 2)
          (F.localTildeAction H hHF) h (Additive.ofMul w))) = ⊤ := by
  let U := F.UH H
  let hUF := F.UH_le_H H hHF
  let c := F.tildeMap U hUF
  let i : V →* U := inclusion (le_conjugateSpanBy V H)
  let f := c.comp i
  have hk : f.ker = (F.Vi 1).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    change F.tildeProjection _ = 1 ↔ _
    exact QuotientGroup.eq_one_iff _
  have hkc : Nat.card f.ker = 2 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 1)).toEquiv]
    exact F.card 1 (by decide)
  have hfc : Nat.card f.range = 2 := by
    have hh := f.ker.card_mul_index
    rw [index_ker,hkc,hV] at hh
    omega
  obtain ⟨w,hw,hu⟩ := (Nat.card_eq_two_iff' (1 : f.range)).mp hfc
  have hw' : (w : F.tilde U) ≠ 1 := by
    intro he
    exact hw (Subtype.ext he)
  have hs (v : V) : f v = 1 ∨ f v = w.val := by
    by_cases hv : f v = 1
    · exact Or.inl hv
    · exact Or.inr (congrArg Subtype.val (hu ⟨f v,⟨v,rfl⟩⟩
        (fun he => hv (congrArg Subtype.val he))))
  refine ⟨w.val,hw',?_,?_⟩
  · intro s
    have hN := hVN s.property
    have hm : F.localTildeAction H hHF s w.val ∈ f.range := by
      obtain ⟨v,hv⟩ := w.property
      have hx : (s : H).val*v.val*(s : H).val⁻¹ ∈ V :=
        (mem_normalizer_iff.mp hN v.val).mp v.property
      refine ⟨⟨_,hx⟩,?_⟩
      rw [←hv]
      change c (i _) = F.localTildeAction H hHF s (c (i v))
      exact (F.tildeAction_apply_map H U hHF hUF
        (le_normalizer_conjugateSpanBy V H) s (i v)).symm
    have hmne : F.localTildeAction H hHF s w.val ≠ 1 := by
      intro he
      exact hw' ((F.localTildeAction H hHF s).map_eq_one_iff.mp he)
    exact congrArg Subtype.val (hu ⟨_,hm⟩ (fun he => hmne (congrArg Subtype.val he)))
  · apply Representation.conjugateSpan_binary_orbit_span V H U
      (le_conjugateSpanBy V H) rfl c (F.tildeMap_surjective U hUF)
      (F.localTildeAction H hHF) ?_ w.val hs
    intro h x hx
    exact (F.tildeAction_apply_map H U hHF hUF
      (le_normalizer_conjugateSpanBy V H) h x).symm

/-- The literal source U/Z has marked binary pentagon coordinates, with
the original point and closure retained. -/
theorem source_index_five_module_marking
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hi : (T : Subgroup G).relIndex H = 5) :
    ∃ he : IsElementaryAbelian 2 (rankTwoSeed T M), letI := he
    ∃ (F : InvariantFlag T (rankTwoSeed T M) 2) (hHF : H ≤ F.H),
      F.Vi 1 = centralInvolutions T ∧
      F.UH H = conjugateSpanBy (localModule T M) H ∧
      ∃ htilde : IsElementaryAbelian 2 (F.tilde (F.UH H)), letI := htilde
      let ρ := Representation.elementaryRepresentation (p := 2) (F.localTildeAction H hHF)
      ∃ (w : Additive (F.tilde (F.UH H))) (a : H),
        w ≠ 0 ∧ orderOf a = 5 ∧
        ((∃ e : BinaryPentagon.Space ≃ₗ[ZMod 2] Additive (F.tilde (F.UH H)),
          (∀ i : Fin 5, e (BinaryPentagon.vertex i) = ρ (a ^ i.val) w) ∧
          (∀ v, e (BinaryPentagon.rotate v) = ρ a (e v))) ∨
        (∃ e : (BinaryPentagon.Space ⧸ BinaryPentagon.constantLine) ≃ₗ[ZMod 2]
            Additive (F.tilde (F.UH H)),
          (∀ i : Fin 5, e (Submodule.Quotient.mk (BinaryPentagon.vertex i)) = ρ (a ^ i.val) w) ∧
          (∀ v, e (Submodule.Quotient.mk (BinaryPentagon.rotate v)) =
            ρ a (e (Submodule.Quotient.mk v))))) := by
  have hm := source_index_five_models hG T hempty hM hu hmany hcard e H hH hi
  obtain ⟨he,F,hp,_,_,hloc⟩ := source_lemma_14_2_6 hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨hHF,h,_,_,_,hk⟩ := hloc H hH
  let htilde : IsElementaryAbelian 2 (F.tilde (F.UH H)) := h.tilde_U_elementary
  let := htilde
  have hV : Nat.card (rankTwoSeed T M) = 4 := by
    rw [rankTwoSeed_eq_localModule]
    exact hcard
  obtain ⟨w,hw,hfix,hspan⟩ := tilde_seed_orbit F H hHF hH.1.2 h.T_normalizes_V hV
  let ρ := Representation.elementaryRepresentation (p := 2) (F.localTildeAction H hHF)
  have hlow := index_five_tilde_finrank_ge_four F H hHF hk hm
  obtain ⟨a,ha,hmark⟩ := BinaryPentagon.marked_orbit_equivalence ρ
    (T.subtype hH.1.2) hi (Additive.ofMul w)
    (fun s => congrArg Additive.ofMul (hfix s)) hspan hlow
  refine ⟨he,F,hHF,hp,?_,htilde,Additive.ofMul w,a,hw,ha,hmark⟩
  change conjugateSpanBy (rankTwoSeed T M) H = _
  rw [rankTwoSeed_eq_localModule]

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
