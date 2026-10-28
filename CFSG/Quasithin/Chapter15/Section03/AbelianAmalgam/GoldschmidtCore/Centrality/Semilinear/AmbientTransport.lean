module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.FixedSpan
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PPerfectHom

/-!
# Ambient transport from the marked plane

The full intersection conclusion of 15.3.46 forces an element preserving
two distinct four-subgroups of V to lie in M: its intersection V∩Vᵍ
would otherwise be totally singular, whereas such a subspace has order
at most four. Since X_E is outside M and normalizes E, its span of F
cannot remain F. In the constructed natural three-space it is therefore
all of W.

Two-perfectness of the actual X_E kills its cubic quotient character.
The resulting commutation of its conjugation with the cubic operator
transports the plane-span equality to ⟨V^{X_E}⟩=U. Finally the genuine
product G_E=Y_E X_E T_E identifies this X_E-span with the ambient V_E.
These lemmas retain the actual subgroups and conjugation maps throughout.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.46, 15.3.66–68, printed pp.1141–1142 and 1152–1155.
-/

@[expose] public section
open Subgroup Stellmacher Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem singular_card_le_four (V M A : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M) (hAV : A ≤ V)
    (hs : ∀ a : A, d.singular ⟨a,hAV a.property⟩) : Nat.card A ≤ 4 := by
  let f : A →* Multiplicative OrthogonalFourBinary.Plane :=
    { toFun := fun a => Multiplicative.ofAdd (d.coordinates ⟨a,hAV a.property⟩).toAdd.1
      map_one' := by
        change Multiplicative.ofAdd (d.coordinates 1).toAdd.1 = 1
        rw [map_one]; rfl
      map_mul' := by
        intro a b
        change Multiplicative.ofAdd (d.coordinates
          ((⟨a,hAV a.property⟩ : V) * ⟨b,hAV b.property⟩)).toAdd.1 = _
        rw [map_mul]; rfl }
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro a ha
    by_contra hn
    have hne : (d.coordinates ⟨a,hAV a.property⟩).toAdd ≠ 0 := by
      intro hz
      have h := d.coordinates.injective (hz.trans (map_one d.coordinates).symm)
      exact hn (Subtype.ext (congrArg (fun v : V => (v : G)) h))
    exact (OrthogonalFourBinary.singular_components _ hne (hs a)).1 ha
  have hc := Nat.card_le_card_of_injective f hf
  have ht : Nat.card (Multiplicative OrthogonalFourBinary.Plane) = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  exact hc.trans_eq ht

/-- The full source-46 intersection assertion prevents an element outside M
from preserving two distinct singular four-groups in V. -/
theorem two_planes_normalizer_le (V M E F : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M)
    (hEV : E ≤ V) (hFV : F ≤ V) (hE : Nat.card E = 4) (hF : Nat.card F = 4)
    (hne : F ≠ E)
    (h46 : ∀ g : G, g ∉ M → ∀ v : V,
      (v : G) ∈ V.map (MulAut.conj g).toMonoidHom → d.singular v) :
    normalizer (E : Set G) ⊓ normalizer (F : Set G) ≤ M := by
  intro g hg
  by_contra hgm
  have hJN : g ∈ normalizer ((E ⊔ F : Subgroup G) : Set G) :=
    normalizer_inf_normalizer_le_normalizer_sup E F hg
  have hJV : E ⊔ F ≤ V := sup_le hEV hFV
  have hsing (a : ↥(E ⊔ F)) : d.singular ⟨a,hJV a.property⟩ := by
    apply h46 g hgm
    refine mem_map.mpr ⟨MulAut.conj (g⁻¹) a,?_,?_⟩
    · exact hJV ((mem_normalizer_iff.mp ((normalizer ((E ⊔ F : Subgroup G) : Set G)).inv_mem hJN) a).mp a.property)
    · simp [MulAut.conj_apply, mul_assoc]
  have hc := singular_card_le_four V M (E ⊔ F) d hJV hsing
  have he : E = E ⊔ F := eq_of_le_of_card_ge le_sup_left (by omega)
  exact hne (eq_of_le_of_card_ge (he ▸ le_sup_right) (by omega))

/-- In a binary three-space the X-span of the source plane is all of W.
Source 46 excludes a preserved plane, using the actual ambient X outside M. -/
theorem plane_X_span_eq (V M E F W X : Subgroup G)
    (d : OrthogonalFourBinary.NaturalAction V M)
    (hEV : E ≤ V) (hFV : F ≤ V) (hE : Nat.card E = 4) (hF : Nat.card F = 4)
    (hne : F ≠ E)
    (h46 : ∀ g : G, g ∉ M → ∀ v : V,
      (v : G) ∈ V.map (MulAut.conj g).toMonoidHom → d.singular v)
    (hXE : X ≤ normalizer (E : Set G)) (hXM : ¬ X ≤ M)
    (hFW : F ≤ W) (hXW : X ≤ normalizer (W : Set G)) (hW : Nat.card W = 8) :
    conjugateSpanBy F X = W := by
  let D := conjugateSpanBy F X
  have hFD : F ≤ D := le_conjugateSpanBy F X
  have hDW : D ≤ W := conjugateSpanBy_le hFW hXW
  by_contra hneDW
  have hdvd : Nat.card D ∣ 8 := hW ▸ card_dvd_of_le hDW
  have hDge : 4 ≤ Nat.card D := hF ▸ Nat.card_le_card_of_injective _ (inclusion_injective hFD)
  have hDlt : Nat.card D < 8 := by
    have hnecard : Nat.card D ≠ Nat.card W := fun he =>
      hneDW (eq_of_le_of_card_ge hDW he.symm.le)
    exact hW ▸ lt_of_le_of_ne (Nat.card_le_card_of_injective _ (inclusion_injective hDW)) hnecard
  have hD : Nat.card D = 4 := by
    have hh : Nat.card D ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hdvd,by decide⟩
    have hdiv : Nat.divisors 8 = {1,2,4,8} := by decide +kernel
    rw [hdiv] at hh
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    omega
  have hDF : D = F := (eq_of_le_of_card_ge hFD (by omega)).symm
  have hXF : X ≤ normalizer (F : Set G) := hDF ▸ le_normalizer_conjugateSpanBy F X
  exact hXM ((le_inf hXE hXF).trans (two_planes_normalizer_le V M E F d hEV hFV hE hF hne h46))

private theorem intrinsic_twoResidual_eq (P : Subgroup G) :
    twoResidualSubgroup P = pResidual 2 P := by
  unfold twoResidualSubgroup pResidual
  congr 1
  ext N
  constructor
  · rintro ⟨hN, hn⟩
    exact ⟨hN, IsPGroup.iff_card.mpr (by simpa only [index_eq_card] using hn)⟩
  · rintro ⟨hN, hn⟩
    exact ⟨hN, by simpa only [index_eq_card] using hn.exists_card_eq⟩

/-- The actual embedded residual X_E is two-perfect. -/
theorem lineX_twoPerfect (E : Subgroup G) : IsPPerfect 2 (lineX E) := by
  unfold lineX twoResidualAmbient
  rw [intrinsic_twoResidual_eq]
  exact isPPerfect_embedded_pResidual 2 (centralizer (E : Set G))

/-- The actual two-residual X_E is killed by the cubic quotient character. -/
theorem lineX_le_characterKernel (H B E : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) (hXH : lineX E ≤ H) :
    lineX E ≤ characterKernel H B hHB := by
  have hp := lineX_twoPerfect E
  have htwo : IsPGroup 2 (MulAut (B ⧸ localTwoCore B)) :=
    IsPGroup.of_card ((ExternalQuotient.aut_card B hc).trans (pow_one 2).symm)
  have he := hp.hom_eq_one_of_isPGroup htwo ((quotientAction H B hHB).comp (inclusion hXH))
  intro x hx
  refine mem_map.mpr ⟨⟨x,hXH hx⟩,?_,rfl⟩
  exact DFunLike.congr_fun he ⟨x,hx⟩

omit [Finite G] in
/-- Cubic commutation transports the plane's X-span into the full source span.
All actions in the proof are literal ambient conjugation. -/
theorem X_span_eq_of_cubic_pair (H B V F U W X : Subgroup G)
    [IsElementaryAbelian 2 U]
    (hHB : H ≤ normalizer (B : Set G)) (hHU : H ≤ normalizer (U : Set G))
    (hBU : B ≤ normalizer (U : Set G))
    (h0U : ambientTwoCore B ≤ centralizer (U : Set G))
    (hVU : V ≤ U) (hXH : X ≤ H) (hXK : X ≤ characterKernel H B hHB)
    (b : B)
    (hV : V = F ⊔ F.map (MulAut.conj (b : G)).toMonoidHom)
    (hW : W = conjugateSpanBy F X)
    (hU : U = W ⊔ W.map (MulAut.conj (b : G)).toMonoidHom) :
    conjugateSpanBy V X = U := by
  let D := conjugateSpanBy V X
  have hFV : F ≤ V := le_sup_left.trans hV.ge
  have hWD : W ≤ D := hW ▸ conjugateSpanBy_mono hFV le_rfl
  have hXχ (x : X) : quotientAction H B hHB ⟨x,hXH x.property⟩ = 1 := by
    obtain ⟨h,hh,hhx⟩ := hXK x.property
    have he : h = ⟨x,hXH x.property⟩ := Subtype.ext hhx
    exact he ▸ hh
  apply le_antisymm (conjugateSpanBy_le hVU (hXH.trans hHU))
  rw [hU]
  refine sup_le hWD ?_
  apply map_le_iff_le_comap.mpr
  rw [hW]
  apply (closure_le _).mpr
  rintro _ ⟨x,hx,f,hf,rfl⟩
  let xx : H := ⟨x,hXH hx⟩
  let ff : Additive U := Additive.ofMul ⟨f,hVU (hFV hf)⟩
  have hi := LinearMap.congr_fun
    (externalCubicAction_intertwining H B U hHB hHU hBU h0U xx (QuotientGroup.mk' _ b)) ff
  have hχ : quotientAction H B hHB xx = 1 := hXχ ⟨x,hx⟩
  rw [hχ] at hi
  have he := congrArg (fun v : Additive U => (v.toMul : G)) hi
  change x * ((b : G) * f * (b : G)⁻¹) * x⁻¹ =
    (b : G) * (x * f * x⁻¹) * (b : G)⁻¹ at he
  change (b : G) * (x * f * x⁻¹) * (b : G)⁻¹ ∈ D
  rw [← he]
  exact subset_closure ⟨x,hx,(b : G)*f*(b : G)⁻¹,
    hV.ge (mem_sup_right (mem_map.mpr ⟨f,hf,rfl⟩)),rfl⟩

/-- The genuine G_E=Y_E X_E T_E product reduces V_E to its X_E-span. -/
theorem lineV_eq_X_span (T M Y V E : Subgroup G)
    (hTM : T ≤ M) (hYM : Y ≤ M) (hMV : M ≤ normalizer (V : Set G))
    (hproduct : (lineNormalizer E : Set G) =
      (lineY Y E : Set G) * (lineX E : Set G) * (lineT T E : Set G)) :
    lineV V E = conjugateSpanBy V (lineX E) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨g,hg,v,hv,rfl⟩
    have hg' : g ∈ (lineY Y E : Set G) * (lineX E : Set G) * (lineT T E : Set G) := by
      rw [← hproduct]; exact hg
    obtain ⟨_,⟨b,hb,x,hx,rfl⟩,t,ht,rfl⟩ := hg'
    have hbG : b ∈ lineNormalizer E := (lineY_le Y E hb).2
    have hx' : b*x*b⁻¹ ∈ lineX E :=
      (mem_normalizer_iff.mp (lineNormalizer_le_normalizer_lineX E hbG) x).mp hx
    have hbt : b*t ∈ M := M.mul_mem (hYM (lineY_le Y E hb).1) (hTM ht.1)
    have hv' : (b*t)*v*(b*t)⁻¹ ∈ V := (mem_normalizer_iff.mp (hMV hbt) v).mp hv
    refine subset_closure ⟨b*x*b⁻¹,hx',(b*t)*v*(b*t)⁻¹,hv',?_⟩
    group
  · exact conjugateSpanBy_mono le_rfl
      ((lineX_le_centralizer E).trans (centralizer_le_normalizer (E : Set G)))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear
