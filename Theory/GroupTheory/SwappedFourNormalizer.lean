module
public import Theory.GroupTheory.SwappedSylowNormalizer
public import GorensteinWalter.KleinFourFixedAutomorphism

/-!
# Normalizers of a half subgroup in a product of four-groups

An order-eight subgroup projecting onto two self-centralizing Klein four
subgroups has a two-group normalizer. Each projection kernel has order two,
so every normalizing element fixes its nonidentity element. Its action on
the opposite four-group consequently has square one. Self-centralization
then gives fourth power one in each coordinate.

This supplies the index-two intersection calculation for the small odd-prime
PSL₂ branch of Aschbacher--Smith 10.2.5, printed p.748. The original quotient
application retains the actual factor exchange and full Sylow projections.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SylowNormalizerAction
variable {Q : Type*} [Group Q]

private theorem first_pow_four (U : Subgroup (Q × Q)) (hu : Nat.card U = 8)
    [IsKleinFour (U.map (MonoidHom.fst Q Q))]
    (hc : centralizer (U.map (MonoidHom.fst Q Q) : Set Q) = U.map (MonoidHom.fst Q Q))
    (hs : Nat.card (U.map (MonoidHom.snd Q Q)) = 4)
    {g : Q × Q} (hg : g ∈ normalizer (U : Set (Q × Q))) : g.1 ^ 4 = 1 := by
  let f : U →* Q := (MonoidHom.snd Q Q).comp U.subtype
  have hr : f.range = U.map (MonoidHom.snd Q Q) := by
    ext x
    exact ⟨fun ⟨u,he⟩ => ⟨u,u.property,he⟩,fun ⟨u,hu,he⟩ => ⟨⟨u,hu⟩,he⟩⟩
  have hk : Nat.card f.ker = 2 := by
    have hh := f.ker.card_mul_index
    rw [index_ker,hr,hs,hu] at hh
    omega
  obtain ⟨v,hv,hunique⟩ := (Nat.card_eq_two_iff' (1 : f.ker)).mp hk
  have hv1 : (v.val.val).1 ≠ 1 := by
    intro he
    apply hv
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext he
    exact v.property
  have hvU : (v.val.val).1 ∈ U.map (MonoidHom.fst Q Q) := mem_map_of_mem _ v.val.property
  have hvfix : g * v.val.val * g⁻¹ = v.val.val := by
    let w : U := ⟨g * v.val.val * g⁻¹,(mem_normalizer_iff.mp hg _).mp v.val.property⟩
    have hw : w ∈ f.ker := by
      change g.2 * v.val.val.2 * g.2⁻¹ = 1
      have he : v.val.val.2 = 1 := v.property
      rw [he,mul_one,mul_inv_cancel]
    have hw1 : (⟨w,hw⟩ : f.ker) ≠ 1 := by
      intro he
      have he' := congrArg (fun z : f.ker => z.val.val) he
      have hv' : v.val.val = 1 := (MulAut.conj g).injective (he'.trans (map_one _).symm)
      exact hv (Subtype.ext (Subtype.ext hv'))
    exact congrArg (fun z : f.ker => z.val.val) (hunique _ hw1)
  let V := U.map (MonoidHom.fst Q Q)
  have hgV : g.1 ∈ normalizer (V : Set Q) :=
    le_normalizer_map (MonoidHom.fst Q Q) (mem_map_of_mem _ hg)
  let a := V.normalizerMonoidHom ⟨g.1,hgV⟩
  have ha : a ^ 2 = 1 := GorensteinWalter.mulAut_sq_eq_one_of_fixed_ne_one a
    (show (⟨v.val.val.1,hvU⟩ : V) ≠ 1 from fun he => hv1 (congrArg Subtype.val he))
    (Subtype.ext (congrArg Prod.fst hvfix))
  have hgsq : g.1 ^ 2 ∈ centralizer (V : Set Q) := by
    have hh : (⟨g.1,hgV⟩ : normalizer (V : Set Q)) ^ 2 ∈ V.normalizerMonoidHom.ker := by
      change V.normalizerMonoidHom (_ ^ 2) = 1
      rw [map_pow]
      exact ha
    rw [normalizerMonoidHom_ker] at hh
    exact hh
  have hgsqV : g.1 ^ 2 ∈ V := hc.le hgsq
  have hh := congrArg Subtype.val (IsKleinFour.mul_self (⟨g.1 ^ 2,hgsqV⟩ : V))
  change g.1 ^ 2 * g.1 ^ 2 = 1 at hh
  simpa only [←pow_add] using hh

/-- The normalizer of an order-eight subdirect subgroup of two self-centralizing
four-groups is a two-group. -/
theorem four_product_half_normalizer (U : Subgroup (Q × Q)) (hu : Nat.card U = 8)
    [IsKleinFour (U.map (MonoidHom.fst Q Q))]
    [IsKleinFour (U.map (MonoidHom.snd Q Q))]
    (hc₁ : centralizer (U.map (MonoidHom.fst Q Q) : Set Q) = U.map (MonoidHom.fst Q Q))
    (hc₂ : centralizer (U.map (MonoidHom.snd Q Q) : Set Q) = U.map (MonoidHom.snd Q Q)) :
    IsPGroup 2 (normalizer (U : Set (Q × Q))) := by
  let e : MulAut (Q × Q) := MulEquiv.prodComm
  let W := U.map e.toMonoidHom
  have hf : W.map (MonoidHom.fst Q Q) = U.map (MonoidHom.snd Q Q) := by
    rw [Subgroup.map_map]; rfl
  have hs : W.map (MonoidHom.snd Q Q) = U.map (MonoidHom.fst Q Q) := by
    rw [Subgroup.map_map]; rfl
  let : IsKleinFour (W.map (MonoidHom.fst Q Q)) := hf.symm ▸ inferInstance
  intro g
  refine ⟨2,Subtype.ext (Prod.ext ?_ ?_)⟩
  · exact first_pow_four U hu hc₁ IsKleinFour.card_four g.property
  · have hg : e g.val ∈ normalizer (W : Set (Q × Q)) :=
      le_normalizer_map e.toMonoidHom (mem_map_of_mem _ g.property)
    exact first_pow_four W (by rw [card_map_of_injective e.injective]; exact hu)
      (by rw [hf]; exact hc₂) (by rw [hs]; exact IsKleinFour.card_four) hg
end Theory.GroupTheory.SylowNormalizerAction
