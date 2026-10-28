module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalThompson
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalThompsonGeometry

/-!
# Equality of the original natural S₇ Thompson and Baumann images

The full natural submodule embeds into the original elementary module V.
Its J(T)-fixed vectors lie in Ω₁(Z(J(T))), so Baum(T) fixes them. The literal
natural fixed-space fixer is the three-swap group. Thus the Baumann image
is bounded by the already marked Thompson image; the reverse inclusion
is the defining centrality of Ω₁(Z(J(T))).

Source: Aschbacher–Smith C.1.24, printed p.131, specialized to R = T.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
open ChapterB BinaryPermutation
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem thompson_le_baumann (R : Subgroup G) :
    elementaryAbelianMaxJ R ≤ baumann R := by
  apply le_inf (sSup_le fun _ hB => hB.1)
  apply le_centralizer_iff.mpr
  intro x hx
  exact mem_centralizer_iff.mpr
    ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2

/-- A natural embedding suffices for Baumann control; it need not exhaust V. -/
theorem natural_baumann_image_eq_of_thompson_marking
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (T : Sylow 2 G) (hVT : V ≤ T)
    (q : G →* Equiv.Perm (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set G))
    (s : core (Fin 7) →ₗ[ZMod 2] Additive V) (hs : Function.Injective s)
    (he : ∀ g v, s (coreRepresentation (Fin 7) g v) =
      NormalElementaryQuotient.representation V q hq hk g (s v))
    (a : Equiv.Perm (Fin 7))
    (ha : (elementaryAbelianMaxJ (T : Subgroup G)).map q =
      (ChapterB.Offenders.D 7).map (MulAut.conj a).toMonoidHom) :
    (baumann (T : Subgroup G)).map q = (elementaryAbelianMaxJ (T : Subgroup G)).map q := by
  let ρ := NormalElementaryQuotient.representation V q hq hk
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let E := V ⊓ centralizer (J : Set G)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le (show E ≤ V from inf_le_left)
  have hEa : E ≤ omegaOneCenterAmbient J :=
    elementary_centralizer_maxJ_le_omegaCenter (T : Subgroup G) E
      (inf_le_left.trans hVT) inf_le_right
  apply le_antisymm
  · rw [ha]
    rintro x ⟨g, hg, rfl⟩
    apply natural_fixed_space_fixer_le_conjugate_D a
    intro v hv
    let w := s v
    have hwfix : w ∈ fixedSpace ρ (J.map q) := by
      rw [show J.map q = (ChapterB.Offenders.D 7).map (MulAut.conj a).toMonoidHom from ha]
      intro z
      change ρ z (s v) = s v
      rw [← he]
      exact congrArg s (hv z)
    have hwE : (w.toMul : G) ∈ E :=
      ⟨w.toMul.property, (NormalElementaryQuotient.mem_fixedSpace_image V q hq hk J w).mp hwfix⟩
    have hgfix : g ∈ centralizer (omegaOneCenterAmbient J : Set G) := hg.2
    have hcomm := mem_centralizer_iff.mp hgfix _ (hEa hwE)
    have hwg : ρ (q g) w = w := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [NormalElementaryQuotient.representation_apply, ← hcomm, mul_inv_cancel_right]
    apply hs
    rw [he]
    exact hwg
  · exact map_mono (thompson_le_baumann _)

/-- Both source images, and their order, in one simultaneous three-pair marking. -/
theorem natural_thompson_baumann_images
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (T : Sylow 2 G) (hVT : V ≤ T)
    (q : G →* Equiv.Perm (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set G))
    (hc : ∀ A, fixedCodim (NormalElementaryQuotient.representation V q hq hk) A =
      fixedCodim (coreRepresentation (Fin 7)) A)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker)
    (s : core (Fin 7) →ₗ[ZMod 2] Additive V) (hs : Function.Injective s)
    (he : ∀ g v, s (coreRepresentation (Fin 7) g v) =
      NormalElementaryQuotient.representation V q hq hk g (s v)) :
    ∃ a : Equiv.Perm (Fin 7),
      (elementaryAbelianMaxJ (T : Subgroup G)).map q =
        pairElementary.map (MulAut.conj a).toMonoidHom ∧
      (baumann (T : Subgroup G)).map q =
        pairElementary.map (MulAut.conj a).toMonoidHom ∧
      Nat.card ((baumann (T : Subgroup G)).map q) = 8 := by
  obtain ⟨a, ha⟩ := natural_source_thompson_conjugate V T hVT q hq hk hc hJ
  have hb := natural_baumann_image_eq_of_thompson_marking V T hVT q hq hk s hs he a ha
  rw [natural_D_eq_pairElementary] at ha
  refine ⟨a, ha, hb.trans ha, ?_⟩
  rw [hb, ha, card_map_of_injective (MulAut.conj a).injective, pairElementary_card]

/-- The source application using the literal natural quotient module. -/
theorem natural_thompson_baumann_images_of_natural_coordinates
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (T : Sylow 2 G) (hVT : V ≤ T)
    (q : G →* Equiv.Perm (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set G))
    (hc : ∀ A, fixedCodim (NormalElementaryQuotient.representation V q hq hk) A =
      fixedCodim (naturalRepresentation (Fin 7)) A)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker)
    (s : natural (Fin 7) →ₗ[ZMod 2] Additive V) (hs : Function.Injective s)
    (he : ∀ g v, s (naturalRepresentation (Fin 7) g v) =
      NormalElementaryQuotient.representation V q hq hk g (s v)) :
    ∃ a : Equiv.Perm (Fin 7),
      (elementaryAbelianMaxJ (T : Subgroup G)).map q =
        pairElementary.map (MulAut.conj a).toMonoidHom ∧
      (baumann (T : Subgroup G)).map q =
        pairElementary.map (MulAut.conj a).toMonoidHom ∧
      Nat.card ((baumann (T : Subgroup G)).map q) = 8 := by
  let hodd : Odd (Fintype.card (Fin 7)) := by decide
  let e := coreEquivNatural (Fin 7) hodd
  have heq (g : Equiv.Perm (Fin 7)) (v : core (Fin 7)) :
      e (coreRepresentation (Fin 7) g v) = naturalRepresentation (Fin 7) g (e v) :=
    coreEquivNatural_equivariant (Fin 7) hodd g v
  apply natural_thompson_baumann_images V T hVT q hq hk
    (fun A => (hc A).trans
      (Representation.BinaryOffender.OddTransport.fixedCodim_eq_of_equivariant
        (coreRepresentation (Fin 7)) (naturalRepresentation (Fin 7)) e heq A).symm)
    hJ (s.comp e.toLinearMap) (hs.comp e.injective)
  intro g v
  change s (e (coreRepresentation (Fin 7) g v)) =
    NormalElementaryQuotient.representation V q hq hk g (s (e v))
  rw [heq, he]

end CFSG.Quasithin.ChapterC.RankOne.Alternating.SevenSource
