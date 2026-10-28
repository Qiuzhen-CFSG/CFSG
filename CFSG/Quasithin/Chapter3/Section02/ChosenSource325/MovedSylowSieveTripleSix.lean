module
public import Theory.Representation.Quotient
public import Theory.Representation.HexacodeAction.EvenBinaryRecognition
public import Theory.Representation.HexacodeAction.ThompsonOffenders
public import Theory.Representation.TripleSixOuterDisplacement
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.SixParabolicTypes


/-!
# Common offenders determine the covered-A₆ constituent

Every offender on the six-dimensional even hexacode is conjugate to its
plane-fixing four-group. An automorphism fixing such a group induces a natural
S₆ automorphism on the actual A₆ quotient. The full hexacode group supplies
its linear intertwiner, and perfectness identifies the original cover action.
Six-dimensional recognition then identifies two faithful constituents sharing
an offender, with the acting group unchanged.

This is the covered-A₆ exclusion in Aschbacher--Smith D.3.5(5), printed p.196,
using B.4.2(8) and K.1.3. The literal application is
`SeedAlternativesMovedSylowTripleSix`. The imported hexacode constructions
retain the licensed ATLAS code and source attribution in `LICENSES/ATLAS.txt`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Atlas.Codes
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open Representation.Hexacode Representation.Hexacode.ThompsonOffenders

theorem hex_offender_conjugate_plane (A : Subgroup HexEvenAutomorphisms)
    (hA : IsOffender evenAction A) :
    ∃ g : HexEvenAutomorphisms, A.map (MulAut.conj g).toMonoidHom = SylowModel.planeGroup := by
  let : IsElementaryAbelian 2 A := hA.1.2
  obtain ⟨S,hS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq HexEvenAutomorphisms S standardSylow
  have hs : (S : Subgroup HexEvenAutomorphisms).map (MulAut.conj g).toMonoidHom =
      SylowModel.sylowGroup := congrArg Sylow.toSubgroup hg
  have hbest := (isBestOffender_iff_of_not_strong evenAction no_strong A).mpr
    ⟨hA.1, (offender_dimensions A hA).2.2.1.trans (offender_dimensions A hA).1.symm⟩
  have ho := (hbest.map_conj evenAction g).isOffender evenAction
  have hc := (offender_dimensions _ ho).2.1
  have he := SylowModel.fourGroup_exhaustion _ ho.1.2
    (hs ▸ Subgroup.map_mono hS) hc
  exact ⟨g,he.resolve_left (fun h => lineGroup_not_offender (h ▸ ho))⟩

theorem hex_even_twist_of_stable_offender (a : MulAut HexEvenAutomorphisms)
    (A : Subgroup HexEvenAutomorphisms) (hA : IsOffender evenAction A)
    (ha : A.map a.toMonoidHom = A) :
    ∃ d : hexacode ≃ₗ[ZMod 2] hexacode,
      ∀ g v, d (evenAction g v) = evenAction (a g) (d v) := by
  let : IsQuasisimple HexEvenAutomorphisms := even_isQuasisimple
  let : IsElementaryAbelian 2 A := hA.1.2
  let q := even_quotient_center_equiv
  let β := MulAut.centralQuotientAction q a
  let F := A.map hexEvenCoordinate
  have hf := injective_comp_subtype_of_coprime_ker hexEvenCoordinate
    (by rw [hexEven_kernel_card]; decide : Nat.Coprime 2 (Nat.card hexEvenCoordinate.ker))
    A (IsElementaryAbelian.isPGroup 2 A)
  have hcF : Nat.card F = 4 := by
    have he : Nat.card (hexEvenCoordinate.comp A.subtype).range = Nat.card A :=
      Nat.card_congr (MonoidHom.ofInjective hf).symm.toEquiv
    rw [MonoidHom.range_comp,Subgroup.range_subtype] at he
    rw [show Nat.card F = Nat.card A from he]
    exact (offender_dimensions A hA).2.1
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map _
  let : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcF]; decide)
  let : IsKleinFour F := ⟨hcF,IsElementaryAbelian.exponent_eq_prime⟩
  have hβ (g : HexEvenAutomorphisms) : β (hexEvenCoordinate g) = hexEvenCoordinate (a g) :=
    MulAut.centralQuotientAction_apply q a g
  have hF : F.map β.toMonoidHom = F := by
    rw [Subgroup.map_map]
    have he : β.toMonoidHom.comp hexEvenCoordinate = hexEvenCoordinate.comp a.toMonoidHom :=
      MonoidHom.ext hβ
    rw [he,←Subgroup.map_map,ha]
  obtain ⟨s,hs⟩ := AlternatingSix.ShadowLocal.FourNormalizers.SixParabolics.four_stabilizer_natural F β hF
  obtain ⟨x,hx⟩ := hexCoordinateSix_surjective s
  have he : MulAut.conjNormal x = a := by
    apply MulAut.centralQuotientAction_injective q
    apply MulEquiv.ext
    intro y
    obtain ⟨g,rfl⟩ := hexEvenCoordinate_surjective y
    rw [show ((MulAut.centralQuotientAction q) (MulAut.conjNormal x)) (hexEvenCoordinate g) =
      hexEvenCoordinate (MulAut.conjNormal x g) from
        MulAut.centralQuotientAction_apply q (MulAut.conjNormal x) g]
    change hexEvenCoordinate (MulAut.conjNormal x g) = β (hexEvenCoordinate g)
    rw [←hs]
    apply Subtype.ext
    change hexCoordinateSixHom (x * g.val * x⁻¹) = s * hexCoordinateSixHom g.val * s⁻¹
    simp only [map_mul,map_inv,hx]
  refine ⟨hexAction x,?_⟩
  intro g v
  have hg := congrArg (fun f : MulAut HexEvenAutomorphisms => (f g).val) he
  change x * g.val * x⁻¹ = (a g).val at hg
  have heq : x * g.val = (a g).val * x := mul_inv_eq_iff_eq_mul.mp hg
  have hh := congrArg (fun z => action z v) heq
  simpa [action,evenAction] using hh


theorem hex_even_twist_of_common_offender (a : MulAut HexEvenAutomorphisms)
    (A : Subgroup HexEvenAutomorphisms) (hA : IsOffender evenAction A)
    (ha : IsOffender evenAction (A.map a.toMonoidHom)) :
    ∃ d : hexacode ≃ₗ[ZMod 2] hexacode,
      ∀ g v, d (evenAction g v) = evenAction (a g) (d v) := by
  obtain ⟨p,hp⟩ := hex_offender_conjugate_plane A hA
  obtain ⟨q,hq⟩ := hex_offender_conjugate_plane (A.map a.toMonoidHom) ha
  let g := p⁻¹ * q
  have hg : (A.map a.toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
    apply Subgroup.map_injective (f := (MulAut.conj p).toMonoidHom) (MulAut.conj p).injective
    rw [Subgroup.map_map]
    have he : (MulAut.conj p).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj q).toMonoidHom := by
      apply MonoidHom.ext
      intro x
      simp [g,MulAut.conj_apply,mul_assoc]
    rw [he,hq,hp]
  let b := a.trans (MulAut.conj g)
  have hb : A.map b.toMonoidHom = A := by
    change A.map ((MulAut.conj g).toMonoidHom.comp a.toMonoidHom) = A
    rw [←Subgroup.map_map]
    exact hg
  obtain ⟨d,hd⟩ := hex_even_twist_of_stable_offender b A hA hb
  refine ⟨d.trans (hexAction (g.val⁻¹)),?_⟩
  intro k v
  change hexAction (g.val⁻¹) (d (evenAction k v)) =
    evenAction (a k) (hexAction (g.val⁻¹) (d v))
  rw [hd]
  have he : g.val⁻¹ * (b k).val = (a k).val * g.val⁻¹ := by
    change g.val⁻¹ * (g.val * (a k).val * g.val⁻¹) = _
    group
  have hh := congrArg (fun z => action z (d v)) he
  simpa [action,evenAction] using hh

theorem six_dimensional_equiv_of_common_offender
    {U Z : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup Z] [Module (ZMod 2) Z]
    [FiniteDimensional (ZMod 2) U] [FiniteDimensional (ZMod 2) Z]
    (τ : Representation (ZMod 2) HexEvenAutomorphisms U)
    (σ : Representation (ZMod 2) HexEvenAutomorphisms Z)
    (ht : Function.Injective τ) (hs : Function.Injective σ)
    (hit : IsIrreducible τ) (his : IsIrreducible σ)
    (hU : Module.finrank (ZMod 2) U = 6) (hZ : Module.finrank (ZMod 2) Z = 6)
    (A : Subgroup HexEvenAutomorphisms) (hA : IsOffender τ A) (hB : IsOffender σ A) :
    Nonempty (Representation.Equiv τ σ) := by
  obtain ⟨a,e,he⟩ := EvenBinaryRecognition.exists_equivariant τ ht hit hU
  obtain ⟨b,f,hf⟩ := EvenBinaryRecognition.exists_equivariant σ hs his hZ
  let c := a.symm.trans b
  have hAe := hA.map_equivariant τ evenAction a.toMonoidHom a.injective e he
  have hBe := hB.map_equivariant σ evenAction b.toMonoidHom b.injective f hf
  have hc : (A.map a.toMonoidHom).map c.toMonoidHom = A.map b.toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    exact congrArg b (a.symm_apply_apply x)
  obtain ⟨d,hd⟩ := hex_even_twist_of_common_offender c (A.map a.toMonoidHom) hAe (hc ▸ hBe)
  refine ⟨Representation.Equiv.mk (e.trans (d.trans f.symm)) ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  change f.symm (d (e (τ g v))) = σ g (f.symm (d (e v)))
  apply f.injective
  rw [f.apply_symm_apply,he,hd,hf,f.apply_symm_apply]
  change evenAction (b (a.symm (a g))) (d (e v)) = evenAction (b g) (d (e v))
  rw [a.symm_apply_apply]


theorem six_dimensional_equiv_of_marked_common_offender
    {K U Z : Type*} [Group K]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup Z] [Module (ZMod 2) Z]
    [FiniteDimensional (ZMod 2) U] [FiniteDimensional (ZMod 2) Z]
    (τ : Representation (ZMod 2) K U) (σ : Representation (ZMod 2) K Z)
    (ht : Function.Injective τ) (hs : Function.Injective σ)
    (hit : IsIrreducible τ) (his : IsIrreducible σ)
    (e : K ≃* HexEvenAutomorphisms)
    (hU : Module.finrank (ZMod 2) U = 6) (hZ : Module.finrank (ZMod 2) Z = 6)
    (A : Subgroup K) (hA : IsOffender τ A) (hB : IsOffender σ A) :
    Nonempty (Representation.Equiv τ σ) := by
  let τ' := τ.comp e.symm.toMonoidHom
  let σ' := σ.comp e.symm.toMonoidHom
  have hit' : IsIrreducible τ' :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective τ).mpr hit
  have his' : IsIrreducible σ' :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective σ).mpr his
  have hi (g : K) (v : U) : τ g v = τ' (e g) v := by
    simp only [τ',MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply]
  have hj (g : K) (v : Z) : σ g v = σ' (e g) v := by
    simp only [σ',MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply]
  obtain ⟨d⟩ := six_dimensional_equiv_of_common_offender τ' σ'
    (ht.comp e.symm.injective) (hs.comp e.symm.injective) hit' his' hU hZ
    (A.map e.toMonoidHom)
    (hA.map_equivariant τ τ' e.toMonoidHom e.injective (LinearEquiv.refl _ _) hi)
    (hB.map_equivariant σ σ' e.toMonoidHom e.injective (LinearEquiv.refl _ _) hj)
  refine ⟨Representation.Equiv.mk d.toLinearEquiv ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  change d (τ g v) = σ g (d v)
  have he := IntertwiningMap.isIntertwining _ _ d.toIntertwiningMap (e g) v
  simpa only [τ',σ',MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    e.symm_apply_apply,Representation.Equiv.toLinearEquiv_apply,
    Representation.Equiv.coe_toIntertwiningMap] using he

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
