module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Action
public import Theory.GroupTheory.Amalgam.NormalBaseRecognition

/-!
# Extending marked reduced endpoints over the original full Borel

Given actual reduced endpoint markings and an equivariant marking of the
original Borel, normal-supplement gluing extends both endpoint maps.
The reduced-intersection theorem supplies the exact overlap; agreement
there and the conjugation identities make the extension well defined.
The resulting amalgam isomorphism retains the prescribed Borel map and
both reduced endpoint restrictions.

This is the conditional reconstruction step in DGS, Groups and Graphs
(1985), (15.2)–(15.3), printed pp.226–231. The source-specific construction
of the permissible model action remains separate. In particular a binary
Ree type statement or a Hall–Janko parabolic equivalence does not provide
the compatible markings required here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open SuzukiContainment
variable {G H : Type*} [Group G] [Group H]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- An equivariant reduced endpoint marking extends over the whole original Borel. -/
theorem exists_original_endpoint_equiv (h : HypothesisF11 L S) (i : Fin 2)
    (R : Subgroup H) (e : parabolic L (reducedSylow L S) i ≃* R)
    (ρ : commonBorel L S →* H)
    (hinter : ∀ b : commonBorel L S, ρ b ∈ R ↔
      (b : G) ∈ commonBorel L (reducedSylow L S))
    (hagree : ∀ b : commonBorel L (reducedSylow L S),
      (e (inclusion (commonBorel_le_parabolic i) b) : H) =
        ρ (inclusion (reduced_commonBorel_le h) b))
    (hconj : ∀ (b : commonBorel L S) (n : parabolic L (reducedSylow L S) i),
      (e (reducedEndpointAction h i b n) : H) = ρ b * e n * (ρ b)⁻¹) :
    ∃ E : parabolic L S i ≃* (R ⊔ ρ.range : Subgroup H),
      (∀ n : parabolic L (reducedSylow L S) i,
        (E (inclusion (reduced_parabolic_le h i) n) : H) = e n) ∧
      ∀ b : commonBorel L S,
        (E (inclusion (commonBorel_le_parabolic i) b) : H) = ρ b := by
  let P := parabolic L S i
  let N := (parabolic L (reducedSylow L S) i).subgroupOf P
  let T := (commonBorel L S).subgroupOf P
  let := reduced_parabolic_normal h i
  let d := subgroupOfEquivOfLe (reduced_parabolic_le h i)
  let t := subgroupOfEquivOfLe (commonBorel_le_parabolic (L := L) (S := S) i)
  let v : T →* H := ρ.comp t.toMonoidHom
  have hgen : N ⊔ T = ⊤ := by
    rw [← subgroupOf_sup (reduced_parabolic_le h i) (commonBorel_le_parabolic i),
      reduced_parabolic_supplement h i]
    exact subgroupOf_self _
  have hi (b : T) : v b ∈ R ↔ (b : P) ∈ N := by
    change ρ (t b) ∈ R ↔ (b : P) ∈ N
    rw [hinter]
    change ((b : P) : G) ∈ commonBorel L (reducedSylow L S) ↔
      ((b : P) : G) ∈ parabolic L (reducedSylow L S) i
    rw [← reduced_parabolic_inf_borel h i]
    exact ⟨fun hb => hb.1, fun hb => ⟨hb, b.property⟩⟩
  have ha (b : T) (hb : (b : P) ∈ N) :
      ((d.trans e) ⟨b, hb⟩ : H) = v b := by
    have hb0 : ((b : P) : G) ∈ commonBorel L (reducedSylow L S) := by
      rw [← reduced_parabolic_inf_borel h i]
      exact ⟨hb, b.property⟩
    exact hagree ⟨b, hb0⟩
  have hc (b : T) (n : N) :
      ((d.trans e) (MulAut.conjNormal (b : P) n) : H) =
        v b * (d.trans e) n * (v b)⁻¹ := by
    exact hconj (t b) (d n)
  obtain ⟨E, hEN, hET⟩ := RankTwoAmalgam.NormalBaseRecognition.exists_endpoint_equiv
    N T R (d.trans e) v hgen hi ha hc
  have hv : v.range = ρ.range := by
    ext y
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨t b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨t.symm b, congrArg ρ (t.apply_symm_apply b)⟩
  let E' := E.trans (MulEquiv.subgroupCongr (congrArg (R ⊔ ·) hv))
  refine ⟨E', ?_, ?_⟩
  · intro n
    exact hEN (d.symm n)
  · intro b
    exact hET (t.symm b)

/-- The original inclusion amalgam, with its full overlap and fixed orientation. -/
@[expose] def originalAmalgam (L : Fin 2 → Subgroup G) (S : Subgroup G) :=
  RankTwoAmalgam.ofSubgroups (parabolic L S 0) (commonBorel L S) (parabolic L S 1)
    (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)

/-- Identify the actual endpoint intersection with the original full Borel,
using the proved F.1.3 intersection equality and unchanged endpoint maps. -/
def originalIntersectionIso (h : HypothesisF11 L S) :
    RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      (originalAmalgam L S) where
  left := MulEquiv.refl _
  middle := MulEquiv.subgroupCongr (lemma_F_1_3_6 h)
  right := MulEquiv.refl _
  left_commutes _ := rfl
  right_commutes _ := rfl

/-- Simultaneous extension retains the prescribed full-Borel map, both endpoint
markings, and both inclusion squares. No type-only branch supplies these inputs. -/
theorem exists_original_amalgam_iso (h : HypothesisF11 L S)
    (R : Fin 2 → Subgroup H)
    (e : ∀ i, parabolic L (reducedSylow L S) i ≃* R i)
    (ρ : commonBorel L S →* H) (hρ : Function.Injective ρ)
    (hinter : ∀ i (b : commonBorel L S), ρ b ∈ R i ↔
      (b : G) ∈ commonBorel L (reducedSylow L S))
    (hagree : ∀ i (b : commonBorel L (reducedSylow L S)),
      (e i (inclusion (commonBorel_le_parabolic i) b) : H) =
        ρ (inclusion (reduced_commonBorel_le h) b))
    (hconj : ∀ i (b : commonBorel L S) (n : parabolic L (reducedSylow L S) i),
      (e i (reducedEndpointAction h i b n) : H) = ρ b * e i n * (ρ b)⁻¹) :
    ∃ E : RankTwoAmalgam.Iso (originalAmalgam L S)
      (RankTwoAmalgam.ofSubgroups (R 0 ⊔ ρ.range) ρ.range (R 1 ⊔ ρ.range)
        le_sup_right le_sup_right),
      E.middle = MonoidHom.ofInjective hρ ∧
      (∀ n : parabolic L (reducedSylow L S) 0,
        (E.left (inclusion (reduced_parabolic_le h 0) n) : H) = e 0 n) ∧
      (∀ n : parabolic L (reducedSylow L S) 1,
        (E.right (inclusion (reduced_parabolic_le h 1) n) : H) = e 1 n) := by
  obtain ⟨E₀, hN₀, hB₀⟩ := exists_original_endpoint_equiv h 0 (R 0) (e 0) ρ
    (hinter 0) (hagree 0) (hconj 0)
  obtain ⟨E₁, hN₁, hB₁⟩ := exists_original_endpoint_equiv h 1 (R 1) (e 1) ρ
    (hinter 1) (hagree 1) (hconj 1)
  refine ⟨{
    left := E₀
    middle := MonoidHom.ofInjective hρ
    right := E₁
    left_commutes := fun b => Subtype.ext (hB₀ b)
    right_commutes := fun b => Subtype.ext (hB₁ b) }, rfl, hN₀, hN₁⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
