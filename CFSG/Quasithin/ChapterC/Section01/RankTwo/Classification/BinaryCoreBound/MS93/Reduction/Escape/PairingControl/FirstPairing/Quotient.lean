module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing

/-!
# The first quotient in MS93 (4.3.2)

The denominator is the actual D_alpha inside the finite vertex stabilizer.
Its normality is relative to that stabilizer. A marking with kernel Q_alpha
descends to G_alpha/D_alpha with kernel exactly Q_alpha/D_alpha. This kernel
is a two-group, so all three extension clauses (A) hold and the Section 1
local normalizers are the full marked parabolic preimages.

This constructs the extension needed by the first application of (1.7).
The selected element, its parabolic closure, and the remaining SourceData
conditions are separate obligations; they are not part of these definitions.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(2), printed p.883;
extension clauses (A), p.828, and local normalizers, p.832.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing
open RankOnePairing
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- D_alpha regarded inside G_alpha. -/
def denominator (a : Vertex R) : Subgroup (stabilizer R a) :=
  (fixedCore R a).subgroupOf (stabilizer R a)

instance denominator_normal (a : Vertex R) : (denominator a).Normal :=
  normal_subgroupOf_of_le_normalizer (fixedCore_normalized a)

/-- The actual source quotient, not a replacement group with the same order. -/
abbrev LocalQuotient (a : Vertex R) := stabilizer R a ⧸ denominator a

def quotientMap (a : Vertex R) : stabilizer R a →* LocalQuotient a :=
  QuotientGroup.mk' (denominator a)

/-- The image of a local subgroup in the source quotient. -/
def quotientImage (a : Vertex R) (H : Subgroup (FreeAmalgam R)) :
    Subgroup (LocalQuotient a) :=
  (H.subgroupOf (stabilizer R a)).map (quotientMap a)

theorem quotientImage_normal (a : Vertex R) (H : Subgroup (FreeAmalgam R))
    (hn : stabilizer R a ≤ normalizer (H : Set (FreeAmalgam R))) :
    (quotientImage a H).Normal :=
  Normal.map (normal_subgroupOf_of_le_normalizer hn) (quotientMap a)
    (QuotientGroup.mk'_surjective _)

theorem quotientImage_eq_bot_iff (a : Vertex R) (H : Subgroup (FreeAmalgam R))
    (hH : H ≤ stabilizer R a) :
    quotientImage a H = ⊥ ↔ H ≤ fixedCore R a := by
  rw [quotientImage, Subgroup.map_eq_bot_iff, quotientMap, QuotientGroup.ker_mk']
  constructor
  · intro h x hx
    exact h (show (⟨x, hH hx⟩ : stabilizer R a) ∈ H.subgroupOf (stabilizer R a) from hx)
  · intro h x hx
    exact h hx

theorem quotientImage_commutator (a : Vertex R) (H K : Subgroup (FreeAmalgam R))
    (hH : H ≤ stabilizer R a) (hK : K ≤ stabilizer R a) :
    quotientImage a ⁅H, K⁆ = ⁅quotientImage a H, quotientImage a K⁆ := by
  have he : ⁅H, K⁆.subgroupOf (stabilizer R a) =
      ⁅H.subgroupOf (stabilizer R a), K.subgroupOf (stabilizer R a)⁆ := by
    apply map_injective (stabilizer R a).subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hH, map_subgroupOf_eq_of_le hK,
      map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup H K).trans (sup_le hH hK))]
  simp only [quotientImage, he, map_commutator]

/-- Vanishing in this quotient means the required bound by D_alpha. -/
theorem quotient_commutator_eq_bot_iff (a : Vertex R)
    (H K : Subgroup (FreeAmalgam R))
    (hH : H ≤ stabilizer R a) (hK : K ≤ stabilizer R a) :
    ⁅quotientImage a H, quotientImage a K⁆ = ⊥ ↔ ⁅H, K⁆ ≤ fixedCore R a := by
  rw [← quotientImage_commutator a H K hH hK]
  exact quotientImage_eq_bot_iff a _ ((Subgroup.commutator_le_sup H K).trans (sup_le hH hK))

/-- Any genuine Q_alpha marking descends through the actual fixed core. -/
def quotientProjection (a : Vertex R) (π : stabilizer R a →* SL)
    (hk : π.ker = (Q R a).subgroupOf (stabilizer R a)) : LocalQuotient a →* SL :=
  QuotientGroup.lift (denominator a) π (by
    rw [hk]
    exact fun _ hx => hx.1)

@[simp] theorem quotientProjection_apply (a : Vertex R) (π : stabilizer R a →* SL)
    (hk : π.ker = (Q R a).subgroupOf (stabilizer R a)) (x : stabilizer R a) :
    quotientProjection a π hk (quotientMap a x) = π x := rfl

theorem quotientProjection_surjective (a : Vertex R) (π : stabilizer R a →* SL)
    (hπ : Function.Surjective π) (hk : π.ker = (Q R a).subgroupOf (stabilizer R a)) :
    Function.Surjective (quotientProjection a π hk) :=
  QuotientGroup.lift_surjective_of_surjective _ π hπ _

theorem quotientProjection_kernel (a : Vertex R) (π : stabilizer R a →* SL)
    (hk : π.ker = (Q R a).subgroupOf (stabilizer R a)) :
    (quotientProjection a π hk).ker = quotientImage a (Q R a) := by
  rw [quotientProjection, QuotientGroup.ker_lift, hk]
  rfl

theorem quotientProjection_kernel_isPGroup [Finite M] (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) (π : stabilizer R a →* SL)
    (hk : π.ker = (Q R a).subgroupOf (stabilizer R a)) :
    IsPGroup 2 (quotientProjection a π hk).ker := by
  rw [quotientProjection_kernel]
  exact (Q_isPGroup R source.two_group source.core_le a ha).comap_subtype.map _

section Extension
variable {A : Type*} [Group A]

theorem extensionCore_eq_kernel (π : A →* SL) (hk : IsPGroup 2 π.ker) :
    extensionCore π = π.ker := by
  have ht : pCore 2 π.ker = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, hk.to_subgroup ⊤⟩)
  rw [extensionCore, ht, ← MonoidHom.range_eq_map, range_subtype]

variable [Finite A]

/-- The two-group-kernel specialization of (A), with its actual common Sylow.
The argument is the extension construction, independent of characteristic
minimality and of later escape conclusions. -/
noncomputable def twoGroupExtension (π : A →* SL) (hπ : Function.Surjective π)
    (hk : IsPGroup 2 π.ker) (flag : SL) (hflag : BinaryWeakBN flag) :
    Extension (M := A) := by
  let B := borelPreimage π flag
  have hb : IsPGroup 2 B := by
    have h := (modelBorelSylow flag).isPGroup'
    rw [coe_modelBorelSylow] at h
    exact h.comap_of_ker_isPGroup π hk
  refine {
    base := {
      projection := π
      surjective := hπ
      flag := flag
      weakBN := hflag
      odd_core := ?_
      odd_index := ?_
      no_supplement := ?_ }
    borel := B
    borel_eq := rfl
    sylow := (hb.to_subgroup ⊤).toSylow (by simp) }
  · apply eq_bot_of_card_eq
    rcases (hk.to_subgroup (pPrimeCore 2 π.ker)).card_eq_or_dvd with h | h
    · exact h
    · exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp
        (pPrimeCore_coprime_card (p := 2) (G := π.ker))) h)
  · have ht : pCore 2 π.ker = ⊤ :=
      top_unique (le_sSup ⟨inferInstance, hk.to_subgroup ⊤⟩)
    rw [ht, index_top]
    decide
  · intro F _
    rw [extensionCore_eq_kernel π hk]
    exact le_sup_right

end Extension

variable [Finite M]

instance localQuotient_finite (a : Vertex R) : Finite (LocalQuotient a) := by
  let := finite_stabilizer R a
  infer_instance

/-- The extension used on p.883, retaining a chosen quotient flag. -/
noncomputable def quotientExtension (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) (π : stabilizer R a →* SL)
    (hπ : Function.Surjective π) (hk : π.ker = (Q R a).subgroupOf (stabilizer R a))
    (flag : SL) (hflag : BinaryWeakBN flag) : Extension (M := LocalQuotient a) :=
  twoGroupExtension (quotientProjection a π hk) (quotientProjection_surjective a π hπ hk)
    (quotientProjection_kernel_isPGroup source a ha π hk) flag hflag

@[simp] theorem quotientExtension_projection (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) (π : stabilizer R a →* SL)
    (hπ : Function.Surjective π) (hk : π.ker = (Q R a).subgroupOf (stabilizer R a))
    (flag : SL) (hflag : BinaryWeakBN flag) :
    (quotientExtension source a ha π hπ hk flag hflag).projection =
      quotientProjection a π hk := rfl

theorem quotientExtension_parabolic (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) (π : stabilizer R a →* SL)
    (hπ : Function.Surjective π) (hk : π.ker = (Q R a).subgroupOf (stabilizer R a))
    (flag : SL) (hflag : BinaryWeakBN flag) (i : Bool) :
    localParabolic (quotientExtension source a ha π hπ hk flag hflag) i =
      parabolic (quotientProjection a π hk) flag i :=
  localParabolic_eq_parabolic _ (quotientProjection_kernel_isPGroup source a ha π hk) i

/-- In this quotient the extension core is precisely the image of Q_alpha. -/
theorem quotientExtension_core (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) (π : stabilizer R a →* SL)
    (hπ : Function.Surjective π) (hk : π.ker = (Q R a).subgroupOf (stabilizer R a))
    (flag : SL) (hflag : BinaryWeakBN flag) :
    extensionCore (quotientExtension source a ha π hπ hk flag hflag).projection =
      quotientImage a (Q R a) := by
  rw [quotientExtension_projection,
    extensionCore_eq_kernel _ (quotientProjection_kernel_isPGroup source a ha π hk),
    quotientProjection_kernel]

/-- The common Sylow is the whole preimage of the marked binary Borel. -/
theorem quotientExtension_commonSylow (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) (π : stabilizer R a →* SL)
    (hπ : Function.Surjective π) (hk : π.ker = (Q R a).subgroupOf (stabilizer R a))
    (flag : SL) (hflag : BinaryWeakBN flag) :
    commonSylow (quotientExtension source a ha π hπ hk flag hflag) =
      borelPreimage (quotientProjection a π hk) flag := by
  change (⊤ : Subgroup (borelPreimage (quotientProjection a π hk) flag)).map
    (borelPreimage (quotientProjection a π hk) flag).subtype = _
  rw [← MonoidHom.range_eq_map, range_subtype]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing
