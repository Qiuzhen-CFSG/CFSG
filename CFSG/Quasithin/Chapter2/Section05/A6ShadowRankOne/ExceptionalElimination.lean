module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.A8Reduction
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.S8Geometry
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.Fusion

/-!
# Eliminating the exceptional A₈ alternative

The marked A₈ extension gives S_C ≃ D₈ and |S| = 256. Its characteristic
cyclic four is TI. Applying the constructed I.7.5 setup and the supplied
square and involution-fusion identities gives exactly two conjugates in T
and |T| = 512. The actual C₂ × S₈ subgroup then has a Sylow subgroup of
half that order. Conjugating it into T transports both characteristic-two
block overgroups, and their generation supplies one outside M.

The outside overgroup has nontrivial two-core, so it meets the extra
hypothesis of 2.3.10. Only then do we obtain β-membership. The bound from
2.3.7(1) supplies subscript-star maximality and contradicts Γe0 = ∅.
Neither β-membership nor Γe0-membership is assumed for the constructed group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 2.5.26, printed pp.568–569. EarlierSelection
records the precise earlier chapter inputs. The Aut(A₆) quotient order and
square identity remain explicit finite-model inputs for the source owner.
-/

public section

open Subgroup
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open CFSG.Quasithin.ChapterI.Section06To08
namespace CFSG.Quasithin.Chapter2.A6ShadowRankOne
variable {G : Type*} [Group G]

/-- Earlier source results used in selection: the involution-centralizer
consequence of 1.1.3(2), 2.3.10 with an actual member of H outside M, and
the half-Sylow upper bound in the proof of 2.3.7(1). -/
structure EarlierSelection (M : Subgroup G) (T : Sylow 2 G) : Prop where
  involution_centralizer : ∀ (g j : G), j ∈ M.map (MulAut.conj g).toMonoidHom → orderOf j = 2 →
    M.map (MulAut.conj g).toMonoidHom ⊓ centralizer ({j} : Set G) ∈ Chapter1.He G
  beta_of_half : ∀ A J : Subgroup G, A ≤ T → A.relIndex T = 2 →
    A ≤ J → J ∈ Chapter1.H G → ¬ J ≤ M → A ∈ beta M
  half_bound : ∀ J ∈ gamma (Chapter1.He G) M, twoPart J ≤ Nat.card T / 2

variable [Finite G]

/-- After placement in a conjugate of T, the two concrete C₂ × S₈ overgroups
supply both the outside-H witness required by 2.3.10 and a member of Γe0.
The transported Sylow subgroup has index two by the proved model order. -/
theorem s8_gammaEvenZero_of_half_sylow (M I : Subgroup G) (T : Sylow 2 G)
    (e : I ≃* X) (U : Sylow 2 I) (a : MulAut G)
    (hUT : (U : Subgroup I).map I.subtype ≤ (T : Subgroup G).map a.toMonoidHom)
    (hout : ¬ I ≤ M.map a.toMonoidHom)
    (hT : Nat.card T = 512)
    (hbeta : ∀ A J : Subgroup G, A ≤ T → A.relIndex T = 2 →
      A ≤ J → J ∈ Chapter1.H G → ¬ J ≤ M → A ∈ beta M)
    (hbound : ∀ J ∈ gamma (Chapter1.He G) M, twoPart J ≤ Nat.card T / 2) :
    ∃ L : Subgroup G, L ∈ gammaEvenZero (Chapter1.He G) M := by
  let B := ((U : Subgroup I).map I.subtype).map a.symm.toMonoidHom
  have hBT : B ≤ T := by
    rintro b ⟨u, hu, rfl⟩
    exact mem_map_equiv.mp (hUT hu)
  have hBcard : Nat.card B = 256 := by
    exact (Nat.card_congr (a.symm.subgroupMap ((U : Subgroup I).map I.subtype)).toEquiv).symm.trans
      (s8_sylow_map_card I e U)
  have hindex : B.relIndex T = 2 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) B T bot_le hBT
    simp only [relIndex_bot_left, hBcard, hT] at hc
    omega
  obtain ⟨L₁, L₂, _, _, _, _, hU₁, hU₂, hgen, hHe₁, hHe₂, hcore₁, hcore₂⟩ :=
    s8_overgroups I e U
  let J₁ := L₁.map a.symm.toMonoidHom
  let J₂ := L₂.map a.symm.toMonoidHom
  have hB₁ : B ≤ J₁ := map_mono hU₁
  have hB₂ : B ≤ J₂ := map_mono hU₂
  have hHeJ₁ : J₁ ∈ Chapter1.He G :=
    map_core_centralizer_le a.symm.toMonoidHom a.symm.injective L₁ 2 hHe₁
  have hHeJ₂ : J₂ ∈ Chapter1.He G :=
    map_core_centralizer_le a.symm.toMonoidHom a.symm.injective L₂ 2 hHe₂
  have hcoreJ₁ : twoCore J₁ ≠ ⊥ :=
    map_pCoreIn_ne_bot a.symm.toMonoidHom a.symm.injective L₁ 2 hcore₁
  have hcoreJ₂ : twoCore J₂ ≠ ⊥ :=
    map_pCoreIn_ne_bot a.symm.toMonoidHom a.symm.injective L₂ 2 hcore₂
  have hgen' : J₁ ⊔ J₂ = I.map a.symm.toMonoidHom := by
    change L₁.map a.symm.toMonoidHom ⊔ L₂.map a.symm.toMonoidHom = _
    rw [← Subgroup.map_sup, hgen]
  have hout' : ¬ I.map a.symm.toMonoidHom ≤ M := by
    intro h
    apply hout
    intro i hi
    exact mem_map_equiv.mpr (h (mem_map_of_mem _ hi))
  have hβ : B ∈ beta M := by
    by_cases h₁ : J₁ ≤ M
    · exact hbeta B J₂ hBT hindex hB₂ hcoreJ₂
        (fun h₂ => hout' (hgen' ▸ sup_le h₁ h₂))
    · exact hbeta B J₁ hBT hindex hB₁ hcoreJ₁ h₁
  obtain ⟨L, _, hL⟩ := exists_gammaEvenZero_of_generating_overgroups
    M (I.map a.symm.toMonoidHom) B J₁ J₂ hgen' hout' hβ hB₁ hB₂
    hHeJ₁ hHeJ₂ hcoreJ₁ hcoreJ₂
    (fun J hJ => by simpa only [hT, hBcard] using hbound J hJ)
  exact ⟨L, hL⟩

/-- The exceptional branch has S_C ≃ D₈, |S| = 256, a TI cyclic four,
exactly its two indicated conjugates in T, and |T| = 512. I.7.5 is used
through the constructed cyclic-four setup in the Fusion module. -/
theorem exceptional_cyclicFour_fusion (d : A8Reduction.LocalData G) (hG : IsQuasithin G)
    (T : Sylow 2 G) (z : G) (hquot : (d.SC.subgroupOf d.S).index = 32)
    (hCT : (T : Subgroup G) ⊓ centralizer ({d.t} : Set G) = d.S)
    (hxT : d.x ∈ T) (hxS : d.x ∉ d.S)
    (hsquares : ∀ (V : Subgroup G) (v : G), V ≤ d.SC → V = zpowers v →
      orderOf v = 4 → v ^ 2 = d.t →
      ∀ a : G, a ∈ d.S → a ∈ centralizer (V : Set G) → orderOf a = 4 →
        a ^ 2 ∈ zpowers d.t ⊔ zpowers z)
    (hfusion : ∀ g : G, MulAut.conj g d.t ∈ zpowers d.t ⊔ zpowers z →
      MulAut.conj g d.t = d.t ∨ MulAut.conj g d.t = MulAut.conj d.x d.t) :
    Nonempty (d.SC ≃* DihedralGroup 4) ∧ Nat.card d.S = 256 ∧
      ∃ (V : Subgroup G) (v : G), V ≤ d.SC ∧ V = zpowers v ∧ orderOf v = 4 ∧
        v ^ 2 = d.t ∧ IsTISubgroup V ∧
        tightConjugateFamily ⊤ V T = {V, conjSubgroup V d.x} ∧ Nat.card T = 512 := by
  obtain ⟨hD, hS, V, v, hVC, hV, hv, ht, hn⟩ :=
    A8Reduction.dihedral_and_cyclicFour_of_localData d hG hquot
  have hST : d.S ≤ T := hCT ▸ inf_le_left
  obtain ⟨hfamily, hcard⟩ := cyclicFour_conjugate_family_and_card V T d.S v d.t z d.x
    hV hv ht T.isPGroup' (hVC.trans (d.core_le_s.trans hST)) hn
    (hsquares V v hVC hV hv ht) hfusion hCT hxT hxS hS
  have hVcard : Nat.card V = 4 := by rw [hV, Nat.card_zpowers, hv]
  let : IsCyclic V := hV ▸ inferInstance
  have htV : d.t ∈ V := ht ▸ V.pow_mem (hV ▸ mem_zpowers v) 2
  exact ⟨hD, hS, V, v, hVC, hV, hv, ht,
    cyclicFour_ti V hVcard d.t htV d.t_order hn, hfamily, hcard⟩

/-- The genuine A₈ alternative is impossible when Γe0 is empty. The
symmetric extension, relative normality of K_i, outside-M placement,
dihedral shape, TI fusion and characteristic-two overgroups are all proved
by the imported constructions and the preceding two theorems. -/
theorem exceptional_branch_impossible (d : A8Reduction.LocalData G) (hG : IsQuasithin G)
    (T : Sylow 2 G) (M : Subgroup G) (z : G)
    (hquot : (d.SC.subgroupOf d.S).index = 32)
    (hCT : (T : Subgroup G) ⊓ centralizer ({d.t} : Set G) = d.S)
    (hxT : d.x ∈ T) (hxS : d.x ∉ d.S)
    (hsquares : ∀ (V : Subgroup G) (v : G), V ≤ d.SC → V = zpowers v →
      orderOf v = 4 → v ^ 2 = d.t →
      ∀ a : G, a ∈ d.S → a ∈ centralizer (V : Set G) → orderOf a = 4 →
        a ^ 2 ∈ zpowers d.t ⊔ zpowers z)
    (hfusion : ∀ g : G, MulAut.conj g d.t ∈ zpowers d.t ⊔ zpowers z →
      MulAut.conj g d.t = d.t ∨ MulAut.conj g d.t = MulAut.conj d.x d.t)
    (hselection : EarlierSelection M T)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅) : False := by
  obtain ⟨_, _, V, v, _, _, _, _, _, _, hT⟩ :=
    exceptional_cyclicFour_fusion d hG T z hquot hCT hxT hxS hsquares hfusion
  obtain ⟨m⟩ := d.smallExtensionModel_nonempty
  let U : Sylow 2 d.smallExtension := Classical.choice inferInstance
  obtain ⟨g, hUT, hout⟩ := d.smallExtension_sylow_placement_outside hG T M U
    hselection.involution_centralizer
  obtain ⟨L, hL⟩ := s8_gammaEvenZero_of_half_sylow M d.smallExtension T m.equiv U (MulAut.conj g)
    hUT hout hT hselection.beta_of_half hselection.half_bound
  simp only [hempty, Set.mem_empty_iff_false] at hL

end CFSG.Quasithin.Chapter2.A6ShadowRankOne
