module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Centralizer.BorelPreimage
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Centralizer.CoveringLayer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.LinearTwo.Centralizer.Displacement

/-!
# The natural L₂ block centralizer calculation

The natural block model and the marked star Borel now agree through the
actual core quotient. The invariant four-group forces a model over a field
of order four. The full Borel preimage is M ∩ L, and its prime-to-three
residual lies in Y₊ by the earlier residual equality.

The covering-module calculation puts all of U(L), including C_U(L), in
that residual. Thus an automorphism fixing Y₊ pointwise fixes U(L) and the
Borel residual. The displacement calculation makes it trivial: it first
acts trivially on L/O₂(L) and L/U(L), then its natural-module cocycle
vanishes, and perfectness kills its remaining central displacement.

Relative normality supplies the conjugation action of I on L, giving
C_I(Y₊) ≤ C_G(L) and hence C_S(Y₊) ≤ C_G(L). These are conditional branch
results: the L₂-block hypothesis, marked Borel and genuine earlier local
conclusions are inputs. The parent exclusion 15.3.30 constructs the block
and uses V₁ ≤ C_S(Y₊) and N_G(V₁) ≤ M for its final contradiction.

Source: Aschbacher–Smith 15.3.30, printed pp.1131–1132; C.1.7–13,
pp.123–125; I.2.3, p.413, combined manuscript of 1 March 2004.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo

variable {G : Type*} [Group G] [Finite G] {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} {m n : ℕ} {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- In the natural L₂-block branch, pointwise fixation of the actual Y₊
forces an automorphism of L to be trivial. The entire central block layer
is accounted for by its containment in the Borel residual. -/
theorem automorphism_eq_one_of_yplus_fixed
    (b : BorelIdentification d I c n F) (h : Earlier d I c)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hblock : ChapterC.IsL2EvenBlock c.L m)
    (hres : d.Yplus = (primeToResidual 3 (d.MI I)).map (d.MI I).subtype)
    (α : MulAut c.L) (hfix : ∀ y ∈ d.Yplus.subgroupOf c.L, α y = y) : α = 1 := by
  let := component_isPerfect_of_containment d c h.contains
  obtain ⟨E, _, _, _, hE, ⟨a⟩⟩ := exists_markedBlockModel_four b h P hP hblock
  have hB := a.blockBorelResidual_le_yplus h P hP hres
  have hU := (blockU_le_blockBorelResidual hblock.2.1 a.model hE).trans hB
  exact automorphism_eq_one_of_blockU_and_borelResidual_fixed a.model α
    (fun u => hfix u (hU u.property)) hE hblock.2.1 (fun x hx => hfix x (hB hx))

/-- Every element of I centralizing Y₊ centralizes L. Normality is only
required inside I, as in 15.3.27(1). -/
theorem local_centralizer_yplus_le_component
    (b : BorelIdentification d I c n F) (h : Earlier d I c)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hblock : ChapterC.IsL2EvenBlock c.L m)
    (hres : d.Yplus = (primeToResidual 3 (d.MI I)).map (d.MI I).subtype) :
    I ⊓ centralizer (d.Yplus : Set G) ≤ centralizer (c.L : Set G) := by
  have hIL : I ≤ normalizer (c.L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (component_le c)).mp h.component_normal
  rintro s ⟨hsI, hsY⟩
  let t : normalizer (c.L : Set G) := ⟨s, hIL hsI⟩
  have ht : c.L.normalizerMonoidHom t = 1 := by
    apply automorphism_eq_one_of_yplus_fixed b h P hP hblock hres
    intro y hy
    apply Subtype.ext
    change s * (y : G) * s⁻¹ = (y : G)
    rw [← hsY y hy, mul_inv_cancel_right]
  have hk : t ∈ c.L.normalizerMonoidHom.ker := ht
  rw [normalizerMonoidHom_ker] at hk
  exact hk

/-- The Sylow centralizer containment used with V₁ in 15.3.30. -/
theorem sylow_centralizer_yplus_le_component
    (b : BorelIdentification d I c n F) (h : Earlier d I c)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hblock : ChapterC.IsL2EvenBlock c.L m)
    (hres : d.Yplus = (primeToResidual 3 (d.MI I)).map (d.MI I).subtype) :
    d.S ⊓ centralizer (d.Yplus : Set G) ≤ centralizer (c.L : Set G) := by
  have hSI : d.S ≤ I := hP ▸ map_subtype_le (P : Subgroup I)
  exact (inf_le_inf_right _ hSI).trans
    (local_centralizer_yplus_le_component b h P hP hblock hres)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo

end
