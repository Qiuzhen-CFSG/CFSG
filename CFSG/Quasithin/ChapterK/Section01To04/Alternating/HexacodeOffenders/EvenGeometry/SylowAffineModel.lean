module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.EvenGeometry.Sylow
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetStabilizer

/-!
# Marked Sylow coordinates in the even affine hexacode group

The full preimage of the explicit dihedral Sylow is an actual Sylow of the
even affine group. Sylow conjugacy preserves the normal translations, so
its original translation marking survives passage to any chosen Sylow.
-/

public noncomputable section
open Subgroup Atlas.Codes Representation
namespace CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders.EvenGeometry.SylowModel
local notation "V" => Multiplicative hexacode
local notation "A" => V ⋊[hexAffineAction.comp hexSign.ker.subtype] HexEvenAutomorphisms
local notation "P" => V ⋊[hexAffineAction.comp (hexSign.ker.subtype.comp sylowGroup.subtype)] sylowGroup

private instance : Finite A := Finite.of_equiv (V × HexEvenAutomorphisms) SemidirectProduct.equivProd.symm
private instance : Finite P := Finite.of_equiv (V × sylowGroup) SemidirectProduct.equivProd.symm

private def embedding : P→*A := SemidirectProduct.map (MonoidHom.id V) sylowGroup.subtype
  (fun _ => MonoidHom.ext fun _ => rfl)

private theorem embedding_injective : Function.Injective embedding := by
  intro x y he
  apply SemidirectProduct.ext
  · exact congrArg (fun z : A => z.left) he
  · apply Subtype.ext
    exact congrArg SemidirectProduct.right he

private theorem embedding_card : Nat.card embedding.range=512 := by
  rw [←Nat.card_congr (MonoidHom.ofInjective embedding_injective).toEquiv,
    SemidirectProduct.card]
  change Nat.card hexacode*Nat.card sylowGroup=512
  rw [hexacode_card,sylowGroup_card]

private def standardAffineSylow : Sylow 2 A := by
  have hp : IsPGroup 2 embedding.range := IsPGroup.of_card (n := 9) (by simpa using embedding_card)
  exact hp.toSylow (by
    have hh := embedding.range.card_mul_index
    have hAc : Nat.card A=69120 := by
      rw [SemidirectProduct.card]
      change Nat.card hexacode*Nat.card HexEvenAutomorphisms=69120
      rw [hexacode_card,hexEven_card]
    rw [embedding_card,hAc] at hh
    have hi : embedding.range.index=135 := by omega
    rw [hi]
    decide)

/-- Arbitrary affine Sylows retain the original full translation subgroup
in the explicit standard dihedral-semilinear coordinates. -/
theorem exists_marked_affine_sylow_equiv (S : Sylow 2 A) :
    ∃ e : S≃*P,
      (((SemidirectProduct.inl : V→*A).range).subgroupOf S).map e.toMonoidHom=
        (SemidirectProduct.inl : V→*P).range := by
  let translations : Subgroup A := (SemidirectProduct.inl : V→*A).range
  let : translations.Normal := by
    dsimp only [translations]
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq A S standardAffineSylow
  have hmap : (S : Subgroup A).map (MulAut.conj a).toMonoidHom=embedding.range := by
    change ((a • S : Sylow 2 A) : Subgroup A)=embedding.range
    rw [ha]
    rfl
  let e : S≃*P := ((MulAut.conj a).subgroupMap S).trans
    ((MulEquiv.subgroupCongr hmap).trans (MonoidHom.ofInjective embedding_injective).symm)
  have he (x : S) : embedding (e x)=MulAut.conj a x.val :=
    congrArg Subtype.val ((MonoidHom.ofInjective embedding_injective).apply_symm_apply
      ((MulEquiv.subgroupCongr hmap) ((MulAut.conj a).subgroupMap S x)))
  have hj (x : P) : embedding x∈translations ↔ x∈(SemidirectProduct.inl : V→*P).range := by
    rw [show translations=(SemidirectProduct.inl : V→*A).range from rfl,
      SemidirectProduct.range_inl_eq_ker_rightHom,SemidirectProduct.range_inl_eq_ker_rightHom]
    change (x.right : HexEvenAutomorphisms)=1 ↔ x.right=1
    constructor
    · intro hh
      apply Subtype.ext
      exact hh
    · intro hh
      exact congrArg (fun d : sylowGroup => (d : HexEvenAutomorphisms)) hh
  have hmem (x : S) : e x∈(SemidirectProduct.inl : V→*P).range ↔ x.val∈translations := by
    rw [←hj,he]
    change a*x.val*a⁻¹∈translations ↔ x.val∈translations
    exact (mem_normalizer_iff.mp (show a∈normalizer (translations : Set A) by
      rw [normalizer_eq_top]; trivial) x.val).symm
  refine ⟨e,?_⟩
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hmem x).mpr hx
  · intro hy
    exact ⟨e.symm y,(hmem (e.symm y)).mp (by simpa only [e.apply_symm_apply] using hy),e.apply_symm_apply y⟩

end CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders.EvenGeometry.SylowModel
