module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingInput
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.FactorDihedral
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Reduction

/-!
# The complement automizer in the Sylow contradiction

The action of the contrary Sylow subgroup on `X/O₂(X)` must be compared
with `Aut_{T_I}(P)`, the normalizer action on an actual Sylow-three
complement `P`. The canonical complement isomorphism intertwines these
actions. The factorization `T_I = O₂(X) N_{T_I}(P)` from 1.3.2 and trivial
quotient action of `O₂(X)` show that their images coincide under this
isomorphism. Thus the proved D₈ quotient action supplies the D₈ automizer
used to sieve the genuine embedding alternatives.

The final adapter constructs the existing `XiEmbedding.LocalInput` and
retains `IsSylowIn 2 T_I I₀` separately. This is the additional hypothesis
needed by the corrected intrinsic embedding theorem; no simplicity of
`I₀` or embedding conclusion is assumed. The ambient QTKE hypothesis
supplies intrinsic SQTK. The classification and both generalized-Fitting
case eliminations remain obligations of the source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 1.3.2–4,
printed pp.508–511, and the proof of 15.4.20, printed p.1164.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
variable {G : Type*} [Group G] [Finite G]

/-- The actual complement map identifies its normalizer automizer with
the full quotient action image. The equality of images uses 1.3.2, rather
than a choice of independent coordinates. -/
noncomputable def complement_automizer_equiv_quotient_action
    {X U : Subgroup G} (hXi : X ∈ Chapter1.Xi G U)
    (hU : Chapter1.IsSylowIn 2 U (X ⊔ U))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hq : Chapter1.XiOddQuotient p (Chapter1.XiQuotient X)) (P : Sylow p X) :
    Chapter1.XiEmbedding.automizer U ((P : Subgroup X).map X.subtype) ≃*
      ((quotientAut (pCore 2 X)).comp
        (X.normalizerMonoidHom.comp (inclusion hXi.invariant))).range := by
  change Chapter1.XiMember U X at hXi
  let P₀ := (P : Subgroup X).map X.subtype
  let N := U ⊓ normalizer (P₀ : Set G)
  let e := hXi.ambientSylowQuotientEquiv ho hq P
  let α := (quotientAut (pCore 2 X)).comp
    (X.normalizerMonoidHom.comp (inclusion hXi.invariant))
  let β := P₀.normalizerMonoidHom.comp (inclusion (show N ≤ normalizer (P₀ : Set G) from inf_le_right))
  let γ := (MulAut.congr e).toMonoidHom
  have he (n : N) : γ (β n) = α (inclusion inf_le_left n) := by
    apply MulEquiv.ext
    intro q
    obtain ⟨a,rfl⟩ := e.surjective q
    change e (β n (e.symm (e a))) = α (inclusion inf_le_left n) (e a)
    rw [e.symm_apply_apply]
    change QuotientGroup.mk' (pCore 2 X) _ =
      quotientAut (pCore 2 X) _ (QuotientGroup.mk' (pCore 2 X) _)
    rw [quotientAut_apply_mk]
    rfl
  have hNU : N ≤ U := inf_le_left
  have hcoreU : X.pCoreIn 2 ≤ U :=
    (hXi.normalizer_factor hU hq P).symm ▸ le_sup_left
  have hgen : (X.pCoreIn 2).subgroupOf U ⊔ N.subgroupOf U = ⊤ := by
    rw [← subgroupOf_sup hcoreU hNU, ← hXi.normalizer_factor hU hq P, subgroupOf_self]
  have hcore : ((X.pCoreIn 2).subgroupOf U).map α = ⊥ := by
    apply eq_bot_iff.mpr
    rintro _ ⟨u,hu,rfl⟩
    apply MulEquiv.ext
    intro q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) q
    obtain ⟨a,ha,hae⟩ := hu
    change (a : G) = (u : G) at hae
    have ha1 : QuotientGroup.mk' (pCore 2 X) a = 1 := (QuotientGroup.eq_one_iff _).mpr ha
    change quotientAut (pCore 2 X) _ (QuotientGroup.mk' (pCore 2 X) x) = _
    rw [quotientAut_apply_mk]
    have hx : (X.normalizerMonoidHom (inclusion hXi.invariant u)) x = a*x*a⁻¹ := by
      apply Subtype.ext
      change (u : G)*(x : G)*(u : G)⁻¹ = (a : G)*(x : G)*(a : G)⁻¹
      rw [hae]
    change QuotientGroup.mk' (pCore 2 X) (X.normalizerMonoidHom (inclusion hXi.invariant u) x) = _
    rw [hx,map_mul,map_mul,map_inv,ha1,one_mul,inv_one,mul_one]
    rfl
  have hmap : (N.subgroupOf U).map α = (α.comp (inclusion hNU)).range := by
    ext a
    constructor
    · rintro ⟨n,hn,heq⟩
      exact ⟨⟨n,hn⟩,heq⟩
    · rintro ⟨n,rfl⟩
      exact ⟨inclusion hNU n,n.property,rfl⟩
  have hfull : (α.comp (inclusion hNU)).range = α.range := by
    have hh := congrArg (fun D : Subgroup U => D.map α) hgen
    rw [Subgroup.map_sup,hcore,bot_sup_eq,← MonoidHom.range_eq_map,hmap] at hh
    exact hh
  have hrange : β.range.map γ = α.range := by
    rw [← MonoidHom.range_comp]
    have hh : γ.comp β = α.comp (inclusion hNU) := MonoidHom.ext he
    rw [hh,hfull]
  exact (equivMapOfInjective β.range γ (MulAut.congr e).injective).trans
    (MulEquiv.subgroupCongr hrange)

/-- The D₈ action transfers to the complement automizer appearing in 1.3.4. -/
theorem contrary_complement_automizer_dihedral
    {X U : Subgroup G} (hXi : X ∈ Chapter1.Xi G U)
    (hU : Chapter1.IsSylowIn 2 U (X ⊔ U))
    (e : (X ⧸ pCore 2 X) ≃* Multiplicative (ZMod 3 × ZMod 3))
    (P : Sylow 3 X)
    (hD : Nonempty (((quotientAut (pCore 2 X)).comp
      (X.normalizerMonoidHom.comp (inclusion hXi.invariant))).range ≃* DihedralGroup 4)) :
    Nonempty (Chapter1.XiEmbedding.automizer U ((P : Subgroup X).map X.subtype) ≃*
      DihedralGroup 4) := by
  obtain ⟨d⟩ := hD
  have hq : Chapter1.XiOddQuotient 3 (Chapter1.XiQuotient X) :=
    Or.inl ⟨(order_nine_quotient_structure e).1, (order_nine_quotient_structure e).2.1⟩
  exact ⟨(complement_automizer_equiv_quotient_action hXi hU (by decide : Odd 3) hq P).trans d⟩

/-- The exact local embedding input, retaining the genuine Sylow hypothesis
needed by the corrected intrinsic 1.3.4. -/
theorem contrary_local_embedding_input {K : GroupClass} (hG : IsSimpleQTKE K G)
    {X U H : Subgroup G} (hH : H ∈ Chapter1.H G) (hXH : X ≤ H)
    (P₂ : Sylow 2 H) (hP₂ : (P₂ : Subgroup H).map H.subtype = U)
    (hXi : X ∈ Chapter1.Xi G U)
    (e : (X ⧸ pCore 2 X) ≃* Multiplicative (ZMod 3 × ZMod 3))
    (P : Sylow 3 X) :
    IsSQTK K H ∧
      Chapter1.XiEmbedding.LocalInput 3 U X ((P : Subgroup X).map X.subtype) H ∧
      Chapter1.IsSylowIn 2 U H := by
  have hUH : U ≤ H := hP₂ ▸ map_subtype_le (P₂ : Subgroup H)
  have hq : Chapter1.XiOddQuotient 3 (Chapter1.XiQuotient X) :=
    Or.inl ⟨(order_nine_quotient_structure e).1, (order_nine_quotient_structure e).2.1⟩
  exact ⟨Chapter3.sqtk_of_mem_H hG hH,
    Chapter1.XiEmbedding.localInput_of_mem_Xi hXi ⟨P₂,hP₂⟩ (sup_le hXH hUH)
      (by decide : Odd 3) hq P, ⟨P₂,hP₂⟩⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
