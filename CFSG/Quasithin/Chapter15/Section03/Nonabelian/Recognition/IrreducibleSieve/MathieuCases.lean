module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Input
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Reductions
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.MathieuCases.Cover
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.MathieuCases.Placement
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Inner
public import Theory.Mathieu.M12.Properties.SylowAutomorphisms
public import Theory.Mathieu.M22.Properties.SylowPointwise.Innerness
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Involutions

/-!
# Exclusion of the Mathieu alternatives in the irreducible sieve

For M₁₂ and M₂₂, conjugation by the marked central involution fixes the
component's Sylow subgroup pointwise. The checked automorphism calculations
make this conjugation inner. Centerlessness and the faithful irreducible binary
action then place the involution in the component itself. Its displacement on
each literal source module has rank four, contradicting the marked rank two.
The M₂₄ modules have odd degree. The triple-cover ambient extension is excluded
by the nonsolvable minimal normal subgroup argument in `Cover`.

The final theorem has exactly the source, component and alternative inputs;
all model facts and placement obligations are discharged here.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of 15.3.58,
printed p.1149; G.9.3(0)–(2), pp.353–357; H.11–H.14, pp.392–398.
-/

public section

open Subgroup Representation Representation.BinaryOffender Sporadic.Mathieu
open CFSG.Quasithin.ChapterG.Section09
open CFSG.Quasithin.ChapterH.Section10To12
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.MathieuCases

private theorem m12_inner_of_fixes_sylow (r : MulAut M12) (S : Sylow 2 M12)
    (hS : ∀ x ∈ S, r x = x) : ∃ g : M12, r = MulAut.conj g := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M12 M12SmallPair.commonSylow S
  let e : MulAut M12 := MulAut.conj g
  have hfixed (x : M12) (hx : x ∈ M12SmallPair.sylowCandidate) :
      MulAut.congr e.symm r x = x := by
    have hmem : e x ∈ S := by
      rw [← hg]
      change e x ∈ (M12SmallPair.commonSylow : Subgroup M12).map e.toMonoidHom
      exact mem_map_of_mem e.toMonoidHom hx
    change e.symm (r (e x)) = x
    rw [hS _ hmem]
    exact e.symm_apply_apply x
  apply (MulAut.congr_inner_iff e.symm r).mp
  rcases M12SmallPair.SylowAutomorphisms.eq_one_or_conj_of_fixes_sylow _ hfixed with he | he
  · exact ⟨1, by simpa only [map_one] using he⟩
  · exact ⟨M12SmallPair.z, he⟩

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

private theorem exclude_action {D M : Type*} [Group D] [Finite D]
    [AddCommGroup M] [Module (ZMod 2) M]
    (h : SourceData ρ X T v s) (hK : ComponentData ρ K)
    (σ : Representation (ZMod 2) D M)
    (hi : ∀ (a : MulAut D) (S : Sylow 2 D), (∀ x ∈ S, a x = x) →
      ∃ d : D, a = MulAut.conj d)
    (hd : ∀ d : D, orderOf d = 2 → fixedCodim σ (zpowers d) = 4)
    (he : Quasiequivalent (ρ.comp K.subtype) σ) : False := by
  obtain ⟨e, f, hf⟩ := he
  have hmem := marked_mem_component_of_pointwise_fixers h hK e hi
  let u : K := ⟨v, hmem⟩
  have hu : orderOf u = 2 := (orderOf_coe u).symm.trans h.involution
  have hr := fixedCodim_map_equivariant (ρ.comp K.subtype) σ e.toMonoidHom f hf (zpowers u)
  rw [MonoidHom.map_zpowers] at hr
  change fixedCodim (ρ.comp K.subtype) (zpowers u) = fixedCodim σ (zpowers (e u)) at hr
  rw [hd (e u) ((e.orderOf_eq u).trans hu),
    fixedCodim_zpowers_eq_displacement_rank] at hr
  change Module.finrank (ZMod 2) (displacement ρ v) = 4 at hr
  rw [h.displacement_rank] at hr
  norm_num at hr

/-- G.9.3 cases (0), (1), and (2) are impossible in the irreducible branch
of 15.3.58, including ambient involutions not initially known to lie in `K`. -/
theorem exclude (h : SourceData ρ X T v s) (hK : ComponentData ρ K)
    (ha : Alternative ρ K (s + 1)) : False := by
  cases ha with
  | m12 _ _ he =>
    exact exclude_action h hK m12HeartRepresentation m12_inner_of_fixes_sylow
      M12Calculations.fixedCodim_involution he
  | m22 _ _ he =>
    rcases he with he | he
    · exact exclude_action h hK MathieuCode.m22CodeRepresentation
        M22SylowPointwise.automorphism_inner_of_fixes_sylow
        MathieuCode.m22_code_involution_displacement he
    · exact exclude_action h hK MathieuCode.m22CocodeRepresentation
        M22SylowPointwise.automorphism_inner_of_fixes_sylow
        MathieuCode.m22_cocode_involution_displacement he
  | m24 _ hd _ =>
    apply h.degree_not_odd
    rw [hd]
    decide
  | triple _ _ he =>
    exact not_tripleExtension hK he.some

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.MathieuCases
