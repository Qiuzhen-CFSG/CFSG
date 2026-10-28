module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition.CodeInputs
public import Theory.Representation.HexacodeAction

/-!
# Marking the cubic input by the actual code section

The source B/U is identified with the concrete binary hexacode. Its
literal inclusion and its conjugate form the two summands of P/U from
E.2.14. A cubic acting as the hexacode scalar on B/U and commuting with
the conjugator is therefore fixed-point free on P/U; this also gives the
total dimension twelve. The second summand uses the action of a, where
a is the image of the inverse of the book's conjugator h.

A marked embedding of the full hexacode group supplies the cubic and the
inversion relation for any odd involution. The final application calls
code_obstruction_of_cubic_extension. Constructing this embedding and
placing the odd involution in the source T remain source obligations;
no identification of a mere group-family tag with the concrete model is used.

Source: Aschbacher–Smith, 8.2.8(4–6), printed pp.718–719, and H.16.1(3),
printed p.402. The concrete code is the existing ATLAS port, attributed
in Theory.Representation.HexacodeAction and licensed in LICENSES/ATLAS.txt.
-/

public section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
variable {G H : Type*} [Group G] [Group H] [Finite G]
  (I V U : Subgroup G) [(U.subgroupOf (I.pCoreIn 2)).Normal]
  [(U.subgroupOf (V ⊓ I.pCoreIn 2)).Normal]
  [IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2))]
  [IsElementaryAbelian 2 ((V ⊓ I.pCoreIn 2 : Subgroup G) ⧸
    U.subgroupOf (V ⊓ I.pCoreIn 2))]

/-- The sum of the literal B/U inclusion and its specified conjugate. -/
def codePairMap (ρ : Representation (ZMod 2) H (CoreSection I U)) (a : H) :
    (IntersectionSection I V U × IntersectionSection I V U) →ₗ[ZMod 2] CoreSection I U :=
  (intersectionInclusion I V U).comp (LinearMap.fst _ _ _) +
    ((ρ a).comp (intersectionInclusion I V U)).comp (LinearMap.snd _ _ _)

omit [Finite G] in
theorem codePairMap_apply (ρ : Representation (ZMod 2) H (CoreSection I U))
    (a : H) (b c : IntersectionSection I V U) :
    codePairMap I V U ρ a (b, c) =
      intersectionInclusion I V U b + ρ a (intersectionInclusion I V U c) := by rfl

/-- The native scalar and the two literal conjugate summands construct the
fixed-point-free cubic and total-rank inputs on P/U. -/
theorem code_pair_cubic_inputs
    (ρ : Representation (ZMod 2) H (CoreSection I U)) (a z : H)
    (eB : IntersectionSection I V U ≃ₗ[ZMod 2] hexacode)
    (hpair : Function.Bijective (codePairMap I V U ρ a))
    (hza : Commute z a)
    (hB : ∀ b, ρ z (intersectionInclusion I V U b) =
      intersectionInclusion I V U (eB.symm (Hexacode.action hexZ (eB b)))) :
    (∀ p, ρ z p = p → p = 0) ∧
      Module.finrank (ZMod 2) (CoreSection I U) = 12 := by
  let f := codePairMap I V U ρ a
  have hcomm (p : CoreSection I U) : ρ z (ρ a p) = ρ a (ρ z p) := by
    change (ρ z * ρ a) p = (ρ a * ρ z) p
    rw [← map_mul, ← map_mul, hza.eq]
  have hzpair (b c : IntersectionSection I V U) :
      ρ z (f (b, c)) = f (eB.symm (Hexacode.action hexZ (eB b)),
        eB.symm (Hexacode.action hexZ (eB c))) := by
    simp only [f, codePairMap_apply, map_add, hcomm, hB]
  constructor
  · intro p hp
    obtain ⟨⟨b, c⟩, rfl⟩ := hpair.surjective p
    rw [hzpair] at hp
    have he := hpair.injective hp
    have hzero (w : IntersectionSection I V U)
        (hw : eB.symm (Hexacode.action hexZ (eB w)) = w) : w = 0 := by
      apply eB.injective
      rw [map_zero]
      apply (Hexacode.scalar_fixed_iff _).mp
      have hh := congrArg eB hw
      simpa only [eB.apply_symm_apply] using hh
    have hb := hzero b (congrArg Prod.fst he)
    have hc := hzero c (congrArg Prod.snd he)
    rw [hb, hc]
    exact f.map_zero
  · have hdimB : Module.finrank (ZMod 2) (IntersectionSection I V U) = 6 :=
      eB.finrank_eq.trans hexacode_finrank
    have hd := (LinearEquiv.ofBijective f hpair).finrank_eq
    rw [Module.finrank_prod, hdimB] at hd
    exact hd.symm

/-- A marked full hexacode extension discharges the scalar and dimension
premises of the code obstruction on the original quotient maps. -/
theorem code_obstruction_of_marked_hexacode
    (ρ : Representation (ZMod 2) H (CoreSection I U))
    (D : Subgroup H) (e : D ≃* DihedralGroup 5)
    (j : HexAutomorphisms →* H) (hj : Function.Injective j)
    (u : HexAutomorphisms) (hu : u ^ 2 = 1) (huodd : hexSign u = -1)
    (a : H) (eB : IntersectionSection I V U ≃ₗ[ZMod 2] hexacode)
    (hpair : Function.Bijective (codePairMap I V U ρ a))
    (hza : Commute (j hexZ) a)
    (hB : ∀ b, ρ (j hexZ) (intersectionInclusion I V U b) =
      intersectionInclusion I V U (eB.symm (Hexacode.action hexZ (eB b))))
    (hn : j u ∈ normalizer (D : Set H))
    (htv : Commute (j u) (e.symm (.sr 0) : H))
    (hvz : Commute (e.symm (.sr 0) : H) (j hexZ))
    (hgen : subspaceCommutator ρ ⊤ (zpowers (e.symm (.r 1) : H)) = ⊤) : False := by
  obtain ⟨hzfree, hdim⟩ := code_pair_cubic_inputs I V U ρ a (j hexZ) eB hpair hza hB
  have hz : orderOf (j hexZ) = 3 := (orderOf_injective j hj hexZ).trans hexZ_order
  have ht : (j u) ^ 2 = 1 := by rw [← map_pow, hu, map_one]
  have hinv : j u * j hexZ = j hexZ ^ 2 * j u := by
    have he := hex_conjugation_odd u huodd
    have hzInv : hexZ⁻¹ = hexZ ^ 2 := by
      apply inv_eq_of_mul_eq_one_right
      simpa only [← pow_succ'] using hexZ_cube
    rw [hzInv] at he
    have hh := congrArg j (mul_inv_eq_iff_eq_mul.mp he)
    simpa only [map_mul, map_pow] using hh
  exact code_obstruction_of_cubic_extension I U ρ D e (j hexZ) (j u)
    hz ht hn htv hvz hinv hzfree hdim hgen

end CFSG.Quasithin.Chapter8.Section02.Normalizer.TensorRecognition
