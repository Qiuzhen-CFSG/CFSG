module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors.Centralizers
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.SmallField

/-!+# Field-involution centralizers for linear actors over the field of nine

Projective descent conjugates any involution with nontrivial field image to
the pure field involution. The existing marked S₃ quotient of its centralizer
then transports to the original centralizer, with kernel exactly its two-core.
The abelian centralizer of a linear four-group supplies full ambient tau
containment. This yields every intrinsic E1 clause with image rank one.

Only positioning remains: the original Sylow intersection must be Sylow,
and the actor must not lie in the local two-core. No field involution is
inserted into the original actor or family.

Source: Aschbacher–Smith E.1.2 and E.1.14(6), pp.210, 214;
the latter cites Aschbacher (1982), Lemma 4.10.
-/

public section
open Subgroup GorensteinWalter
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors
variable {F : Type*} [Field F] [Finite F] [Finite (PGammaL2 F)]

private theorem map_centralizer_singleton {G : Type*} [Group G]
    (e : G ≃* G) (x : G) :
    (centralizer ({x} : Set G)).map e.toMonoidHom = centralizer ({e x} : Set G) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e z * e x = e x * e z
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hz)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hy

/-- Every field-involution centralizer has its actual S₃ quotient with
kernel equal to the intrinsic two-core. -/
theorem nine_fieldCentralizer_quotient (hF : Nat.card F = 3 ^ 2)
    (x : PGammaL2 F) (hx : orderOf x = 2) (hfield : x.right ≠ 1) :
    ∃ f : centralizer ({x} : Set (PGammaL2 F)) →* Equiv.Perm (Fin 3),
      Function.Surjective f ∧ f.ker = pCore 2 (centralizer ({x} : Set (PGammaL2 F))) := by
  have hq : IsOddPrimePower (Nat.card F) :=
    ⟨3, 2, Nat.prime_three, by decide, by decide, hF⟩
  obtain ⟨c, hc⟩ := projective_semilinear_involution_conj_inr hq x hx hfield
  let a := MulAut.conj (SemidirectProduct.inl c : PGammaL2 F)⁻¹
  have ha : a x = SemidirectProduct.inr x.right := by
    simpa [a, MulAut.conj_apply] using hc
  have hsq : x.right ^ 2 = 1 := by
    change (SemidirectProduct.rightHom x) ^ 2 = 1
    have hh := congrArg (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F))
      (show x ^ 2 = 1 by simpa only [hx] using pow_orderOf_eq_one x)
    simpa only [map_pow, map_one] using hh
  let C := centralizer ({x} : Set (PGammaL2 F))
  let C' := centralizer ({SemidirectProduct.inr x.right} : Set (PGammaL2 F))
  have hmap : C.map a.toMonoidHom = C' := by
    change (centralizer ({x} : Set (PGammaL2 F))).map a.toMonoidHom = C'
    rw [map_centralizer_singleton, ha]
  let e : C ≃* C' := (C.equivMapOfInjective a.toMonoidHom a.injective).trans
    (MulEquiv.subgroupCongr hmap)
  let q := smallFieldCentralizerQuotient hF x.right hsq hfield
  let f := q.comp e.toMonoidHom
  refine ⟨f, (smallFieldCentralizerQuotient_surjective hF x.right hsq hfield).comp
    e.surjective, ?_⟩
  ext z
  change e z ∈ q.ker ↔ z ∈ pCore 2 C
  rw [(smallFieldCentralizerQuotient_kernel hF x.right hsq hfield).1,
    ← pCore_map_iso 2 e]
  exact mem_map_iff_mem e.injective

/-- For a linear four-group, centralization of a field involution supplies
the full ambient tau condition, without requiring that involution in A. -/
theorem isEMemberAt_nine_fieldCentralizer (hF : Nat.card F = 3 ^ 2)
    (T : Sylow 2 (PGammaL2 F)) (A : Subgroup (PGammaL2 F))
    (hA : IsElementaryAbelian 2 A) (hr : Group.rank A = 2)
    (hAL : A ≤ pGammaL2PGLRange F) (hAT : A ≤ (T : Subgroup _))
    (x : PGammaL2 F) (hx : orderOf x = 2) (hfield : x.right ≠ 1)
    (hcent : x ∈ centralizer (A : Set (PGammaL2 F)))
    (hSyl : ∃ S : Sylow 2 (centralizer ({x} : Set (PGammaL2 F))),
      (S : Subgroup _) = (T : Subgroup _).subgroupOf (centralizer ({x} : Set _)))
    (ha : ¬ A.subgroupOf (centralizer ({x} : Set (PGammaL2 F))) ≤
      pCore 2 (centralizer ({x} : Set (PGammaL2 F)))) :
    IsEMemberAt 1 (T : Subgroup _) A (centralizer ({x} : Set (PGammaL2 F))) := by
  have hAC : A ≤ centralizer ({x} : Set (PGammaL2 F)) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hcent b hb)
  have htau := tau_le_centralizer_of_mem Nat.prime_three (by decide) hF (by decide)
    x.right hfield T A hA hr hAL x hcent
  obtain ⟨f, hf, hk⟩ := nine_fieldCentralizer_quotient hF x hx hfield
  apply PSLThreeGeneration.ProperExtension.GraphThree.isEMemberAt_of_symmetricThree_quotient
    (T : Subgroup _) A _ hA hAT hAC htau hSyl f hf
  · rw [hk]; exact pCore_isPGroup
  · rwa [hk]

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape.RankTwoFamilies.LinearActors
