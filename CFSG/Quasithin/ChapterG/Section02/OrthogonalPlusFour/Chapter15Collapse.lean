module
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse.Algebra
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse.Geometry
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse.Factors
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Model

/-!
# The central middle-layer collapse in the literal Chapter 15 groups

In the G.2.6 substitution, nonorthogonality and the Frattini bounds show
that U ∩ Uᵍ centralizes both W and Wᵍ. Consequently P₀ = V(U ∩ Uᵍ)
is central in P. The original starred Y-map supplies the odd index needed
for its actual coprime conjugation action. The natural module has full
Y-support; a fixed-free upper section identifies P₀ as the preimage of
C_{P/V}(Y). Its fixed factor is T-normal and is therefore trivial by
Ω₁(Z(T)) = Z ≤ V.

`literal_collapse_and_section` applies these steps through all five
published Chapter15 group comparisons. It gives P₀ = V, the two marked
intersection identities, the internal coprime splitting, clause (5), and
conjugation coordinates on P/V identical to those on P/P₀.
`literal_preimage_formula` retains the actual relative-quotient maps, and
`literal_split_product` gives multiplication of the two actual factors.
These small corollaries avoid expensive kernel reduction of their data
through the full geometric proof.

`source_collapse` discharges natural irreducibility and the zero upper
Y-fixed space using the proved geometry and marked module configuration.
`literal_source_collapse` constructs both E₄ isomorphisms, and
`literal_source_application` assembles all five clauses, including the
actual setwise products and the residual-factor natural modules on P/V.
The common printed multiplicity is retained as an explicit clause of the
full earlier G.2.6 conclusion; its source assembly owner must discharge it.
General product recognition alone supplies separate multiplicities.
No legacy G26Witness field or intersection-collapse assumption is used.

Source: Aschbacher–Smith, 15.3.53–54, printed pp.1145–1146,
PDF pp.1162–1163, using G.2.6 on printed p.336.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
open Setup
variable {G : Type*} [Group G] {D : Setup G} {g : G}

/-- View P/V inside I/V using the actual subtype and quotient maps.
Only normality of V inside I is used, never ambient normality. -/
theorem relative_fixed_preimage (I P Y V : Subgroup G)
    (hPI : P ≤ I) (hYI : Y ≤ I) (hVI : V ≤ I)
    (hIV : I ≤ normalizer (V : Set G)) :
    letI : (V.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hIV
    commutatorPreimage P Y V =
      ((P.subgroupOf I ⊓
        (centralizer (((Y.subgroupOf I).map (QuotientGroup.mk' (V.subgroupOf I))) :
          Set (I ⧸ V.subgroupOf I))).comap (QuotientGroup.mk' (V.subgroupOf I))).map
        I.subtype) := by
  let : (V.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hIV
  rw [← commutatorPreimage_eq_inf_comap_centralizer]
  apply le_antisymm
  · have hCI : commutatorPreimage P Y V ≤ I := (commutatorPreimage_le P Y V).trans hPI
    have hc : (commutatorPreimage P Y V).subgroupOf I ≤
        commutatorPreimage (P.subgroupOf I) (Y.subgroupOf I) (V.subgroupOf I) := by
      apply le_commutatorPreimage (show (commutatorPreimage P Y V).subgroupOf I ≤ P.subgroupOf I from
        fun _ hx => commutatorPreimage_le P Y V hx)
      change ⁅(commutatorPreimage P Y V).subgroupOf I, Y.subgroupOf I⁆ ≤ V.comap I.subtype
      rw [← map_le_iff_le_comap, map_commutator, map_subgroupOf_eq_of_le hCI,
        map_subgroupOf_eq_of_le hYI]
      exact commutator_commutatorPreimage_le P Y V (hPI.trans hIV)
    have hm := map_mono (f := I.subtype) hc
    rwa [map_subgroupOf_eq_of_le hCI] at hm
  · apply le_commutatorPreimage
    · exact (map_mono (commutatorPreimage_le (P.subgroupOf I) (Y.subgroupOf I)
        (V.subgroupOf I))).trans (map_subgroupOf_eq_of_le hPI).le
    · have hm := map_mono (f := I.subtype)
        (commutator_commutatorPreimage_le (P.subgroupOf I) (Y.subgroupOf I)
          (V.subgroupOf I) le_normalizer_of_normal)
      rwa [map_commutator, map_subgroupOf_eq_of_le hYI,
        map_subgroupOf_eq_of_le hVI] at hm

/-- The marked-point calculation centralizes the middle layer, before
its collapse. All hypotheses here precede that collapse in the source. -/
theorem central_middle_layer [Finite G] (d : Hypothesis D g)
    (hgen : D.I g = D.L ⊔ D.U) (hsplit : D.S g = coreProduct D g)
    (hST : D.S g ≤ D.T) (hUV : D.U ⊓ D.VL = D.V)
    (hVC : D.VL ≤ centralizer (D.S g : Set G)) :
    D.S₂ g ≤ centralizer (D.W g : Set G) ∧
    D.S₂ g ≤ centralizer (conjugate (D.W g) g : Set G) ∧
    S₂ D g ≤ D.S g ⊓ centralizer (D.S g : Set G) := by
  have hgI : g ∈ D.I g := hgen.symm ▸ mem_sup_left d.g_mem
  have hSU : D.S g ≤ normalizer (D.U : Set G) := hST.trans
    ((normal_subgroupOf_iff_le_normalizer d.closure.normal.1).mp d.closure.normal.2)
  have hSUg : D.S g ≤ normalizer (conjugate D.U g : Set G) := by
    have hm := (map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hSU).trans
      (D.U.le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
    change conjugate (D.S g) g ≤ normalizer (conjugate D.U g : Set G) at hm
    rw [conjugate_core D g hgI] at hm
    exact hm
  have hVLg : D.VL.map (MulAut.conj g⁻¹).toMonoidHom = D.VL :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (D.VL : Set G)).inv_mem (L_normalizes_VL D d.g_mem))
  have hZg : conjugate D.V₁ g ≤ D.VL := by
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (point_le_VL D)
    rwa [hVLg] at hm
  have hUgv : conjugate D.U g ⊓ D.VL = conjugate D.V g := by
    have hm := congrArg (map (MulAut.conj g⁻¹).toMonoidHom) hUV
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective, hVLg] at hm
    exact hm
  have hUZg : D.U ⊓ conjugate D.V₁ g = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    exact d.conjugate_point_inf_V.le ⟨hx.2, hUV ▸ ⟨hx.1, hZg hx.2⟩⟩
  have hUgZ : conjugate D.U g ⊓ D.V₁ = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    exact (point_inf_conjugate_perpendicular d).le
      ⟨hx.2, hUgv ▸ ⟨hx.1, point_le_VL D hx.2⟩⟩
  have hder := derived_le_point d.base d.closure
  have hderg : ⁅conjugate D.U g, conjugate D.U g⁆ ≤ conjugate D.V₁ g := by
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hder
    rwa [map_commutator] at hm
  have hXS : conjugate (D.W g) g ≤ D.S g := by
    rw [conjugate_W D g hgI]
    exact inf_le_right
  have hc := intersection_centralizes_marks
    (show D.W g ≤ D.U from inf_le_left)
    (map_mono (show D.W g ≤ D.U from inf_le_left))
    ((show D.W g ≤ D.S g from inf_le_right).trans hSUg) (hXS.trans hSU)
    hder hderg hUZg hUgZ
  have hEC : D.S₂ g ≤ centralizer (D.S g : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hsplit]
    exact sup_le (le_centralizer_iff.mp hc.1) (le_centralizer_iff.mp hc.2)
  exact ⟨hc.1, hc.2, le_inf (d.layers hgen).2.1 (sup_le hVC hEC)⟩

/-- Zero fixed space in the actual represented section means that its
ambient commutator preimage is exactly its kernel. -/
theorem fixed_preimage_le_of_section
    {I P B Y : Subgroup G} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {ρ : Representation (ZMod 2) I M}
    (s : Representation.BinaryConjugationSection I P B ρ)
    (hPB : P ≤ normalizer (B : Set G)) (hYI : Y ≤ I)
    (hfixed : ∀ v : M, (∀ y : Y, ρ (inclusion hYI y) v = v) → v = 0) :
    commutatorPreimage P Y B ≤ B := by
  intro x hx
  let a : P := ⟨x, commutatorPreimage_le P Y B hx⟩
  have hc : ⁅Y, commutatorPreimage P Y B⁆ ≤ B := by
    rw [commutator_comm]
    exact commutator_commutatorPreimage_le P Y B hPB
  have hv : (s.coordinates a).toAdd = 0 := by
    apply hfixed
    intro y
    exact s.fixed_on_imageSpace_of_commutator_le Y (commutatorPreimage P Y B) hc
      (inclusion hYI y) y.property _
      ((s.mem_imageSpace_iff _ _).mpr ⟨a, hx, rfl⟩)
  exact (s.coordinates_eq_one_iff a).mp (Multiplicative.toAdd.injective hv)

/-- Transporting the kernel preserves the very same coordinates and
conjugation action. Consequently every genuine factor-module decomposition
on M is unchanged when S₂ is identified with V. -/
def section_with_kernel {I P B V : Subgroup G}
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {ρ : Representation (ZMod 2) I M}
    (s : Representation.BinaryConjugationSection I P B ρ) (h : B = V) :
    Representation.BinaryConjugationSection I P V ρ where
  section_le := s.section_le
  kernel_le := h ▸ s.kernel_le
  normalized := s.normalized
  coordinates := s.coordinates
  onto := s.onto
  kernel_eq := s.kernel_eq.trans (congrArg (fun K : Subgroup G => K.subgroupOf P) h)
  equivariant := s.equivariant

theorem section_with_kernel_coordinates {I P B V : Subgroup G}
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {ρ : Representation (ZMod 2) I M}
    (s : Representation.BinaryConjugationSection I P B ρ) (h : B = V) :
    (section_with_kernel s h).coordinates = s.coordinates := rfl



/-- T preserves the natural module because it preserves both the seed
point and its Y-conjugating group. -/
theorem T_normalizes_natural [Finite G] (d : Hypothesis D g) :
    D.T ≤ normalizer (D.VL : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro t ht x ⟨l, hl, z, hz, rfl⟩
  apply Subgroup.subset_closure
  exact ⟨t * l * t⁻¹, le_normalizer_iff.mp d.base.T_normalizes_L t ht l hl,
    t * z * t⁻¹, le_normalizer_iff.mp d.base.T_normalizes_point t ht z hz, by group⟩

/-- The index needed for coprime action is the original starred Y-order,
not the order of Y itself. -/
theorem odd_source_index [Finite G] (d : Hypothesis D g)
    (hgen : D.I g = D.L ⊔ D.U) : Odd ((D.S g).subgroupOf D.L).index := by
  have hstar : D.star (D.I g) = D.star (D.L ⊔ D.U) := congrArg D.star hgen
  have hk : (D.binaryStarRestriction (D.I g) d.I_le_LT).ker = pCore 2 (D.I g) := by
    rw [← d.IStarProjection_ker hstar]
    ext i
    change _ = 1 ↔ d.IStarProjection i = 1
    rw [Subtype.ext_iff]
    rfl
  have hLI : D.L ≤ D.I g := hgen.symm ▸ le_sup_left
  have hind : (D.S g).relIndex D.L = Nat.card (D.star D.L) := by
    calc
      (D.S g).relIndex D.L = (pCore 2 (D.I g)).relIndex (D.L.subgroupOf (D.I g)) := by
        rw [← relIndex_map_map_of_injective _ _ (D.I g).subtype_injective,
          map_subgroupOf_eq_of_le hLI]
        rfl
      _ = (D.binaryStarRestriction (D.I g) d.I_le_LT).ker.relIndex
          (D.L.subgroupOf (D.I g)) := by rw [hk]
      _ = Nat.card ((D.L.subgroupOf (D.I g)).map
          (D.binaryStarRestriction (D.I g) d.I_le_LT)) := relIndex_ker _ _
      _ = Nat.card (D.star D.L) := by rw [binaryStarRestriction_map _ _ _ hLI]
  change Odd ((D.S g).relIndex D.L)
  rw [hind, Nat.card_congr d.L_model.toEquiv]
  norm_num [Nat.card_eq_fintype_card]

/-- The group-theoretic collapse, with the two genuine module consequences
still explicit: V=[V,Y] and the absence of fixed vectors above S₂. -/
theorem collapse_of_fixed_preimage [Finite G] (d : Hypothesis D g)
    (hgen : D.I g = D.L ⊔ D.U) (hsplit : D.S g = coreProduct D g)
    (hST : D.S g ≤ D.T) (hUV : D.U ⊓ D.VL = D.V)
    (hVC : D.VL ≤ centralizer (D.S g : Set G))
    (hVY : ⁅D.VL,D.L⁆ = D.VL)
    (hno : commutatorPreimage (D.S g) D.L (S₂ D g) ≤ S₂ D g)
    (hΩ : omegaCenter D.T ≤ D.VL) :
    commutatorPreimage (D.S g) D.L D.VL = S₂ D g ∧
    S₂ D g = D.VL ⊔ (S₂ D g ⊓ centralizer (D.L : Set G)) ∧
    Disjoint D.VL (S₂ D g ⊓ centralizer (D.L : Set G)) ∧
    D.T ≤ normalizer (S₂ D g ⊓ centralizer (D.L : Set G) : Set G) ∧
    S₂ D g ⊓ centralizer (D.L : Set G) = ⊥ ∧ S₂ D g = D.VL := by
  have hl := d.layers hgen
  have hLI : D.L ≤ D.I g := hgen.symm ▸ le_sup_left
  have hIB : D.I g ≤ normalizer (S₂ D g : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hl.2.2.2.2.trans le_sup_left)
  have hTU : D.T ≤ normalizer (D.U : Set G) :=
    (normal_subgroupOf_iff_le_normalizer d.closure.normal.1).mp d.closure.normal.2
  have hTI : D.T ≤ normalizer (D.I g : Set G) := by
    rw [hgen]
    exact (le_inf d.base.T_normalizes_L hTU).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hTP : D.T ≤ normalizer (D.S g : Set G) :=
    hTI.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 (D.I g)))
  have hT : IsPGroup 2 D.T := by
    obtain ⟨Q, hQ⟩ := d.base.sylow_LT
    rw [← hQ]
    exact Q.isPGroup'.map D.LT.subtype
  exact central_layer_collapse D.T (D.S g) (S₂ D g) D.VL D.L (D.S g)
    hT hST le_sup_left hl.2.1 ((central_middle_layer d hgen hsplit hST hUV hVC).2.2.trans inf_le_right)
    (hLI.trans hIB) hTP (T_normalizes_natural d) d.base.T_normalizes_L
    ((commutator_mono le_rfl hLI).trans hl.2.2.2.2) hVY hno
    le_rfl (odd_source_index d hgen) hΩ



/-- Irreducibility of the actual natural I-module gives full Y-support.
Trivial support would make g fix the marked point, contradicting its
nonorthogonality. -/
theorem natural_commutator_eq_of_irreducible [Finite G] (d : Hypothesis D g)
    (hgen : D.I g = D.L ⊔ D.U)
    (hirr : ∀ A : Subgroup G, A ≤ D.VL → D.I g ≤ normalizer (A : Set G) →
      A = ⊥ ∨ A = D.VL) : ⁅D.VL,D.L⁆ = D.VL := by
  have hIL : D.I g ≤ normalizer (D.L : Set G) := by
    rw [hgen]
    exact sup_le D.L.le_normalizer (d.closure.normal.1.trans d.base.T_normalizes_L)
  have hIC : D.I g ≤ normalizer (⁅D.VL,D.L⁆ : Subgroup G) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (d.I_normalizes_VL hx),
      mem_normalizer_iff_map_conj_eq.mp (hIL hx)]
  have hC : ⁅D.VL,D.L⁆ ≤ D.VL :=
    le_normalizer_iff_commutator_le_left.mp (L_normalizes_VL D)
  rcases hirr _ hC hIC with hzero | hfull
  · have hc := commutator_eq_bot_iff_le_centralizer.mp hzero
    exfalso
    apply d.nonorthogonal
    rintro x ⟨z, hz, rfl⟩
    have he := mem_centralizer_iff.mp (hc (point_le_VL D hz)) g⁻¹ (D.L.inv_mem d.g_mem)
    change g⁻¹ * z * (g⁻¹)⁻¹ ∈ D.V
    rw [he, mul_inv_cancel_right]
    exact d.base.point_le hz
  · exact hfull

open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.Nonabelian

/-- Literal Chapter 15 application of the collapse argument. The upper
fixed-space premise is a consequence of the genuine G.2.6(5) factor
modules. The output keeps their actual section coordinates, ready for
transport of that decomposition. No intersection collapse is assumed. -/
theorem literal_collapse_and_section [Finite G]
    {Z ZS Zperp V Y T : Subgroup G} {g : G}
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (hgen : pairI Z ZS g = Y ⊔ closureU Z ZS)
    (hsplit : (Chapter15.setup Z Zperp Y T).S g =
      coreProduct (Chapter15.setup Z Zperp Y T) g)
    (hPT : pairP Z ZS g ≤ T) (hUV : closureU Z ZS ⊓ V = Zperp)
    (hVC : V ≤ centralizer (pairP Z ZS g : Set G))
    (hirr : ∀ A : Subgroup G, A ≤ V → pairI Z ZS g ≤ normalizer (A : Set G) →
      A = ⊥ ∨ A = V)
    (hΩ : omegaCenter T = Z)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    {ρ : Representation (ZMod 2) (pairI Z ZS g) M}
    (s : Representation.BinaryConjugationSection (pairI Z ZS g) (pairP Z ZS g)
      (V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g)) ρ)
    (hfixed : ∀ v : M,
      (∀ y : pairI Z ZS g, (y : G) ∈ Y → ρ y v = v) → v = 0) :
    let P₀ := V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g)
    commutatorPreimage (pairP Z ZS g) Y V = P₀ ∧
    P₀ = V ⊔ (P₀ ⊓ centralizer (Y : Set G)) ∧
    Disjoint V (P₀ ⊓ centralizer (Y : Set G)) ∧
    T ≤ normalizer (P₀ ⊓ centralizer (Y : Set G) : Set G) ∧
    P₀ ⊓ centralizer (Y : Set G) = ⊥ ∧ P₀ = V ∧
    closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g ≤ V ∧
    closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g =
      Zperp ⊓ rightConjugate Zperp g ∧
    pairW Z ZS g ⊓ rightConjugate (pairW Z ZS g) g =
      closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g ∧
    rightConjugate (pairW Z ZS g) g ≤ normalizer (closureU Z ZS : Set G) ∧
    ⁅rightConjugate (pairW Z ZS g) g, closureU Z ZS⁆ ≤ pairW Z ZS g ∧
    ∃ sV : Representation.BinaryConjugationSection (pairI Z ZS g) (pairP Z ZS g) V ρ,
      sV.coordinates = s.coordinates := by
  let D := Chapter15.setup Z Zperp Y T
  let P₀ := V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g)
  have hu : D.U = closureU Z ZS := Chapter15.closure_eq hZS hperp
  have hi : D.I g = pairI Z ZS g := Chapter15.I_eq g hZS hperp
  have hs : D.S g = pairP Z ZS g := Chapter15.S_eq g hZS hperp
  have hw : D.W g = pairW Z ZS g := Chapter15.W_eq g hZS hperp
  have hv : D.VL = V := Chapter15.VL_eq hspan
  have he : S₂ D g = P₀ := Chapter15.S₂_eq g hZS hperp hspan
  have hgenD : D.I g = D.L ⊔ D.U := by
    rw [hi, hu]
    exact hgen
  have hST : D.S g ≤ D.T := by rw [hs]; exact hPT
  have hUV' : D.U ⊓ D.VL = D.V := by rw [hu,hv]; exact hUV
  have hVC' : D.VL ≤ centralizer (D.S g : Set G) := by rw [hv,hs]; exact hVC
  have hl := d.layers hgenD
  have hIB : D.I g ≤ normalizer (S₂ D g : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hl.2.2.2.2.trans le_sup_left)
  have hPB : pairP Z ZS g ≤ normalizer (P₀ : Set G) := by
    rw [← hs, ← he]
    exact (pCoreIn_le 2 (D.I g)).trans hIB
  have hYI : Y ≤ pairI Z ZS g := hgen.symm ▸ le_sup_left
  have hno := fixed_preimage_le_of_section s hPB hYI (by
    intro v hf
    apply hfixed v
    intro y hy
    exact hf ⟨y,hy⟩)
  have hnoD : commutatorPreimage (D.S g) D.L (S₂ D g) ≤ S₂ D g := by
    rw [hs,he]
    exact hno
  have hmove := natural_commutator_eq_of_irreducible d hgenD (by
    intro A hA hn
    rw [hv] at hA ⊢
    rw [hi] at hn
    exact hirr A hA hn)
  have hΩ' : omegaCenter D.T ≤ D.VL := by
    change omegaCenter T ≤ D.VL
    rw [hΩ]
    exact point_le_VL D
  have hc := collapse_of_fixed_preimage d hgenD hsplit hST hUV' hVC' hmove hnoD hΩ'
  have hBV : P₀ = V := by
    have hh := hc.2.2.2.2.2
    rwa [he,hv] at hh
  have hEV : closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g ≤ V :=
    (le_sup_right : _ ≤ P₀).trans hBV.le
  have hVg : V.map (MulAut.conj g⁻¹).toMonoidHom = V := by
    rw [← hv]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (D.VL : Set G)).inv_mem (L_normalizes_VL D d.g_mem))
  have hUVg : rightConjugate (closureU Z ZS) g ⊓ V = rightConjugate Zperp g := by
    have hh := congrArg (map (MulAut.conj g⁻¹).toMonoidHom) hUV
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective, hVg] at hh
    exact hh
  have hEperp : closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g =
      Zperp ⊓ rightConjugate Zperp g := by
    apply le_antisymm
    · intro x hx
      exact ⟨hUV ▸ ⟨hx.1,hEV hx⟩, hUVg ▸ ⟨hx.2,hEV hx⟩⟩
    · exact inf_le_inf (hUV.symm.le.trans inf_le_left)
        (hUVg.symm.le.trans inf_le_left)
  have hgI : g ∈ pairI Z ZS g := hYI d.g_mem
  have hmark := marked_intersection (D := D) (g := g) (hi.symm ▸ hgI) hl.2.1
  have hmark' : pairW Z ZS g ⊓ rightConjugate (pairW Z ZS g) g =
      closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g := by
    change D.W g ⊓ conjugate (D.W g) g = D.U ⊓ conjugate D.U g at hmark
    rw [hw,hu] at hmark
    exact hmark
  have hfive := Chapter15.conjugate_mark_normalizes hZS hperp d.closure hgI hPT
  rw [hs,hv,he] at hc
  exact ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2.1,hBV,hEV,hEperp,
    hmark',hfive.1,hfive.2,
    section_with_kernel s hBV,rfl⟩

/-- Turn the internal splitting proved above into multiplication of the
actual ambient factors, without carrying quotient-action instances. -/
theorem central_split_product {V B P Y : Subgroup G}
    (hsplit : B = V ⊔ (B ⊓ centralizer (Y : Set G)))
    (hd : Disjoint V (B ⊓ centralizer (Y : Set G)))
    (hBP : B ≤ P) (hVC : V ≤ centralizer (P : Set G)) :
    ∃ e : V × (B ⊓ centralizer (Y : Set G) : Subgroup G) ≃* B,
      ∀ v c, (e (v,c) : G) = (v : G) * (c : G) := by
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting V
    (B ⊓ centralizer (Y : Set G)) hd
    (hVC.trans (centralizer_le (inf_le_left.trans hBP)))
  exact ⟨e.trans (MulEquiv.subgroupCongr hsplit.symm),he⟩

/-- The multiplication isomorphism on the literal Chapter 15 middle
layer. Its split and disjointness inputs are conclusions of
`literal_collapse_and_section`, and its centrality inputs are the earlier
G.2.6 layer conclusions. -/
theorem literal_split_product {Z ZS V Y : Subgroup G} {g : G}
    (hsplit : V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g) =
      V ⊔ ((V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g)) ⊓
        centralizer (Y : Set G)))
    (hd : Disjoint V
      ((V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g)) ⊓ centralizer (Y : Set G)))
    (hBP : V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g) ≤ pairP Z ZS g)
    (hVC : V ≤ centralizer (pairP Z ZS g : Set G)) :
    ∃ e : V × ((V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g)) ⊓
        centralizer (Y : Set G) : Subgroup G) ≃*
        (V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g) : Subgroup G),
      ∀ v c, (e (v,c) : G) = (v : G) * (c : G) :=
  central_split_product hsplit hd hBP hVC

/-- Apply the relative quotient formula to the preimage equality proved by
`literal_collapse_and_section`. Keeping the normality instance at this small
boundary avoids expanding it throughout the geometric proof. -/
theorem literal_preimage_formula {Z ZS V Y : Subgroup G} {g : G}
    (hYI : Y ≤ pairI Z ZS g) (hVI : V ≤ pairI Z ZS g)
    (hIV : pairI Z ZS g ≤ normalizer (V : Set G))
    (hpre : commutatorPreimage (pairP Z ZS g) Y V =
      V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g)) :
    letI : (V.subgroupOf (pairI Z ZS g)).Normal := normal_subgroupOf_of_le_normalizer hIV
    V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g) =
      (((pairP Z ZS g).subgroupOf (pairI Z ZS g) ⊓
        (centralizer ((Y.subgroupOf (pairI Z ZS g)).map
          (QuotientGroup.mk' (V.subgroupOf (pairI Z ZS g))) : Set
            (pairI Z ZS g ⧸ V.subgroupOf (pairI Z ZS g)))).comap
          (QuotientGroup.mk' (V.subgroupOf (pairI Z ZS g)))).map (pairI Z ZS g).subtype) := by
  exact hpre.symm.trans (relative_fixed_preimage (pairI Z ZS g) (pairP Z ZS g) Y V
    (pCoreIn_le 2 (pairI Z ZS g)) hYI hVI hIV)

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse


@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
open Setup Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G}

/-- The genuine marked quotient configuration eliminates the upper Y-fixed
space; natural irreducibility and all structural premises are supplied by
the proved G.2.6 geometry. Only the earlier Omega-center bound remains. -/
theorem source_collapse (d : Hypothesis D g) (hΩ : omegaCenter D.T ≤ D.VL) :
    commutatorPreimage (D.S g) D.L D.VL = S₂ D g ∧
    S₂ D g = D.VL ⊔ (S₂ D g ⊓ centralizer (D.L : Set G)) ∧
    Disjoint D.VL (S₂ D g ⊓ centralizer (D.L : Set G)) ∧
    D.T ≤ normalizer (S₂ D g ⊓ centralizer (D.L : Set G) : Set G) ∧
    S₂ D g ⊓ centralizer (D.L : Set G) = ⊥ ∧ S₂ D g = D.VL := by
  let := moduleSectionNormal d d.I_eq_LU
  let := moduleSectionElementary d d.I_eq_LU d.S_normalizes_U d.S_eq_coreProduct
  obtain ⟨σ, c, _, _, hf⟩ := source_quotient_configuration d d.I_eq_LU
    d.S_normalizes_U d.S_eq_coreProduct d.VL_eq_sup_conjugate_V d.VL_inf_U
    d.quotientSymmetricEquiv d.quotientSymmetricEquiv_L_image
    d.symmetricUFirst d.symmetricUSecond d.quotientSymmetricEquiv_U_image
    d.symmetricImage_U_split.2.1 d.symmetricImage_U_split.2.2
  have hfixed : fixedSpace (σ.comp (moduleProjection d.quotientSymmetricEquiv))
      (D.L.subgroupOf (D.I g)) = ⊥ := by
    rw [fixedSpace_comp_map, moduleProjection, d.quotientSymmetricEquiv_L_image]
    exact hf
  have hno := fixed_preimage_le_of_section c
    ((pCoreIn_le 2 (D.I g)).trans (le_normalizer_iff_commutator_le_left.mpr
      (d.normal_layers.2.2.2.2.trans le_sup_left)))
    (show D.L ≤ D.I g from d.I_eq_LU.symm ▸ le_sup_left) (by
      intro v hv
      have hm : v ∈ fixedSpace (σ.comp (moduleProjection d.quotientSymmetricEquiv))
          (D.L.subgroupOf (D.I g)) := by
        intro l
        exact hv ⟨l, l.property⟩
      rwa [hfixed, Submodule.mem_bot] at hm)
  exact collapse_of_fixed_preimage d d.I_eq_LU d.S_eq_coreProduct d.S_le_T
    (by rw [inf_comm]; exact d.VL_inf_U) (d.central_first_layer.trans inf_le_right)
    (natural_commutator_eq_of_irreducible d d.I_eq_LU d.I_on_VL_irreducible) hno hΩ

open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.Nonabelian

/-- The complete central collapse and both actual E₄ identifications,
with all earlier geometry and upper fixed-space premises discharged. -/
theorem literal_source_collapse
    {Z ZS Zperp V Y T : Subgroup G}
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (hΩ : omegaCenter T = Z) :
    let P₀ := V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g)
    pairI Z ZS g = Y ⊔ closureU Z ZS ∧
    pairP Z ZS g = pairW Z ZS g ⊔ rightConjugate (pairW Z ZS g) g ∧
    V ≤ pairP Z ZS g ⊓ centralizer (pairP Z ZS g : Set G) ∧
    commutatorPreimage (pairP Z ZS g) Y V = P₀ ∧
    P₀ = V ⊔ (P₀ ⊓ centralizer (Y : Set G)) ∧
    Disjoint V (P₀ ⊓ centralizer (Y : Set G)) ∧
    T ≤ normalizer (P₀ ⊓ centralizer (Y : Set G) : Set G) ∧
    P₀ ⊓ centralizer (Y : Set G) = ⊥ ∧ P₀ = V ∧
    closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g ≤ V ∧
    closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g =
      Zperp ⊓ rightConjugate Zperp g ∧
    pairW Z ZS g ⊓ rightConjugate (pairW Z ZS g) g =
      closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g ∧
    Nonempty ((closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g : Subgroup G) ≃*
      Multiplicative (Fin 2 → ZMod 2)) ∧
    Nonempty ((pairW Z ZS g ⊓ rightConjugate (pairW Z ZS g) g : Subgroup G) ≃*
      Multiplicative (Fin 2 → ZMod 2)) ∧
    rightConjugate (pairW Z ZS g) g ≤ normalizer (closureU Z ZS : Set G) ∧
    ⁅rightConjugate (pairW Z ZS g) g, closureU Z ZS⁆ ≤ pairW Z ZS g := by
  let D := Chapter15.setup Z Zperp Y T
  change Hypothesis D g at d
  have hu : D.U = closureU Z ZS := Chapter15.closure_eq hZS hperp
  have hi : D.I g = pairI Z ZS g := Chapter15.I_eq g hZS hperp
  have hs : D.S g = pairP Z ZS g := Chapter15.S_eq g hZS hperp
  have hw : D.W g = pairW Z ZS g := Chapter15.W_eq g hZS hperp
  have hv : D.VL = V := Chapter15.VL_eq hspan
  have he := Chapter15.S₂_eq (T := T) g hZS hperp hspan
  have hΩD : omegaCenter D.T ≤ D.VL := by
    change omegaCenter T ≤ D.VL
    rw [hΩ]
    exact point_le_VL D
  have hc := source_collapse d hΩD
  rw [hs, hv, he] at hc
  have hcontained : closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g ≤ V :=
    le_sup_right.trans hc.2.2.2.2.2.le
  have hmark := marked_intersection (D := D) (g := g) d.g_mem_I d.normal_layers.2.1
  change D.W g ⊓ conjugate (D.W g) g = D.U ⊓ conjugate D.U g at hmark
  rw [hw, hu] at hmark
  have hfour := Chapter15.closureIntersectionEquivOfContained d hZS hperp hspan hcontained
  have hfive := Chapter15.conjugate_mark_normalizes hZS hperp d.closure
    (hi ▸ d.g_mem_I) (hs ▸ d.S_le_T)
  refine ⟨?_, ?_, ?_, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1,
    hc.2.2.2.2.1, hc.2.2.2.2.2, hcontained,
    Chapter15.closure_intersection_eq_of_contained d hZS hperp hspan hcontained,
    hmark, ⟨hfour⟩, ⟨(MulEquiv.subgroupCongr hmark).trans hfour⟩, hfive⟩
  · rw [← hi, ← hu]
    exact d.I_eq_LU
  · change pairP Z ZS g = pairW Z ZS g ⊔ conjugate (pairW Z ZS g) g
    rw [← hs, ← hw]
    exact d.S_eq_coreProduct
  · rw [← hv, ← hs]
    exact d.central_first_layer

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse


@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
open Setup
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
variable {G : Type*} [Group G] [Finite G]

/-- The printed products are actual setwise products, with both original markings. -/
theorem literal_products {Z ZS Zperp Y T : Subgroup G} {g : G}
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g) :
    (pairI Z ZS g : Set G) = (Y : Set G) * (closureU Z ZS : Set G) ∧
    (pairP Z ZS g : Set G) = (pairW Z ZS g : Set G) *
      (rightConjugate (pairW Z ZS g) g : Set G) := by
  let D := Chapter15.setup Z Zperp Y T
  change Hypothesis D g at d
  have hu : D.U = closureU Z ZS := Chapter15.closure_eq hZS hperp
  have hi : D.I g = pairI Z ZS g := Chapter15.I_eq g hZS hperp
  have hs : D.S g = pairP Z ZS g := Chapter15.S_eq g hZS hperp
  have hw : D.W g = pairW Z ZS g := Chapter15.W_eq g hZS hperp
  constructor
  · rw [← hi, ← hu]
    exact d.I_product
  · change (pairP Z ZS g : Set G) = (pairW Z ZS g : Set G) *
      (conjugate (pairW Z ZS g) g : Set G)
    rw [← hs, ← hw]
    exact d.S_product

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse


@[expose] public section
open Subgroup InvertedCubicTensor
open scoped Pointwise
open Representation.BinaryOffender Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
variable {G : Type*} [Group G] [Finite G]
variable {Z ZS Zperp V Y T : Subgroup G} {g : G}
variable {M : Type*} [AddCommGroup M] [Module F M]

/-- Transport of the full G.2.6 module conclusion to the literal Chapter 15
quotient. Equal multiplicities are a clause of that earlier theorem, not
an inferred consequence of quadraticity. All collapse and residual-action
premises are discharged here. -/
theorem literal_module_transport
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (hΩ : omegaCenter T = Z)
    (e : (pairI Z ZS g ⧸ pCore 2 (pairI Z ZS g)) ≃* (S₃ × S₃))
    (hY : (Y.subgroupOf (pairI Z ZS g)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (pairI Z ZS g)))) =
        (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)))
    (σ : Representation F (S₃ × S₃) M)
    (c : Representation.BinaryConjugationSection (pairI Z ZS g) (pairP Z ZS g)
      (V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (pairI Z ZS g))))))
    (r : ProductDecomposition σ) (hsame : r.leftMultiplicity = r.rightMultiplicity) :
    ∃ f : FactorModuleConclusion (pairI Z ZS g) (pairP Z ZS g) V Y
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (pairI Z ZS g)))) σ,
      f.conjugation.coordinates = c.coordinates ∧ f.decomposition = r := by
  have hc := literal_source_collapse hZS hperp hspan d hΩ
  have hBV := hc.2.2.2.2.2.2.2.2.1
  let cV := section_with_kernel c hBV
  have hYI : Y ≤ pairI Z ZS g := hc.1.symm ▸ le_sup_left
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (pairI Z ZS g)))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hr := source_oddFactor_modules π Y hYI hY σ cV r
  refine ⟨{
    conjugation := cV
    decomposition := r
    sameMultiplicity := hsame
    left_residual := hr.1
    right_residual := hr.2
    left_fixed := ?_
    right_fixed := ?_ }, rfl, rfl⟩
  · rw [actorPreimage_fixed π hπ]
    exact r.left_fixed
  · rw [actorPreimage_fixed π hπ]
    exact r.right_fixed

/-- All five clauses of the literal conditional 15.3.54 application.
The earlier 15.3.48/53 setup and the full equal-multiplicity G.2.6 module
conclusion remain the explicit source inputs. No intersection collapse,
upper fixed-space premise or cardinality substitute is assumed. -/
theorem literal_source_application
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (hΩ : omegaCenter T = Z)
    (e : (pairI Z ZS g ⧸ pCore 2 (pairI Z ZS g)) ≃* (S₃ × S₃))
    (hY : (Y.subgroupOf (pairI Z ZS g)).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (pairI Z ZS g)))) =
        (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)))
    (σ : Representation F (S₃ × S₃) M)
    (c : Representation.BinaryConjugationSection (pairI Z ZS g) (pairP Z ZS g)
      (V ⊔ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (pairI Z ZS g))))))
    (r : ProductDecomposition σ) (hsame : r.leftMultiplicity = r.rightMultiplicity) :
    pairI Z ZS g = Y ⊔ closureU Z ZS ∧
    pairP Z ZS g = pairW Z ZS g ⊔ rightConjugate (pairW Z ZS g) g ∧
    (pairI Z ZS g : Set G) = (Y : Set G) * (closureU Z ZS : Set G) ∧
    (pairP Z ZS g : Set G) = (pairW Z ZS g : Set G) *
      (rightConjugate (pairW Z ZS g) g : Set G) ∧
    V ≤ pairP Z ZS g ⊓ centralizer (pairP Z ZS g : Set G) ∧
    closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g =
      Zperp ⊓ rightConjugate Zperp g ∧
    pairW Z ZS g ⊓ rightConjugate (pairW Z ZS g) g =
      closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g ∧
    Nonempty ((closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g : Subgroup G) ≃*
      Multiplicative (Fin 2 → ZMod 2)) ∧
    Nonempty ((pairW Z ZS g ⊓ rightConjugate (pairW Z ZS g) g : Subgroup G) ≃*
      Multiplicative (Fin 2 → ZMod 2)) ∧
    (∃ f : FactorModuleConclusion (pairI Z ZS g) (pairP Z ZS g) V Y
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (pairI Z ZS g)))) σ,
      f.conjugation.coordinates = c.coordinates ∧ f.decomposition = r) ∧
    rightConjugate (pairW Z ZS g) g ≤ normalizer (closureU Z ZS : Set G) ∧
    ⁅rightConjugate (pairW Z ZS g) g, closureU Z ZS⁆ ≤ pairW Z ZS g := by
  obtain ⟨hI, hP, hV, _, _, _, _, _, _, _, hperps, hmarks, hfour, hfourW, hfive⟩ :=
    literal_source_collapse hZS hperp hspan d hΩ
  have hp := literal_products hZS hperp d
  exact ⟨hI, hP, hp.1, hp.2, hV, hperps, hmarks, hfour, hfourW,
    literal_module_transport hZS hperp hspan d hΩ e hY σ c r hsame, hfive⟩

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
