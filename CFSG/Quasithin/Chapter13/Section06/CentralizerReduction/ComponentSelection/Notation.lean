module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.Notation
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Theory.GroupTheory.Covering
public import Theory.GroupTheory.AbelianConjugateSpan

/-!
# Action quotients and the component-selection families

These are the literal subgroups and faithful conjugation quotients used in
13.6.8–16. Star images are obtained by restriction to C_G(v) followed by its
quotient map. The kernel calculation identifies the quotient with the one
by C_{C_G(v)}(U_v), and the induced action is faithful.

The X-families use the two-residual O², whereas Y_z tests the quasisimplicity
of K*/O₂(K*). Membership in Y_z retains the actual Chapter 1 local family.
No assertion of nonemptiness or component selection is part of these definitions.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, combined
1 March 2004 manuscript, printed pp.928–930.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open Subgroup
variable {G : Type*} [Group G]

/-- Restriction of the normalizer action to the given acting subgroup. -/
def conjugationAction (W H : Subgroup G) (h : H ≤ normalizer (W : Set G)) :
    H →* MulAut W := W.normalizerMonoidHom.comp (inclusion h)

theorem conjugationAction_apply (W H : Subgroup G)
    (h : H ≤ normalizer (W : Set G)) (x : H) (w : W) :
    ((conjugationAction W H h x w : W) : G) = (x : G) * w * (x : G)⁻¹ := rfl

/-- The kernel is the relative centralizer, not the ambient centralizer. -/
theorem conjugationAction_ker (W H : Subgroup G) (h : H ≤ normalizer (W : Set G)) :
    (conjugationAction W H h).ker = (centralizer (W : Set G)).subgroupOf H := by
  ext x
  change conjugationAction W H h x = 1 ↔ (x : G) ∈ centralizer (W : Set G)
  rw [mem_centralizer_iff]
  constructor
  · intro hx w hw
    have he := congrArg (fun f : MulAut W => ((f ⟨w, hw⟩ : W) : G)) hx
    change (x : G) * w * (x : G)⁻¹ = w at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hx
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change (x : G) * (w : G) * (x : G)⁻¹ = (w : G)
    rw [← hx w w.property]
    simp [mul_assoc]

/-- U_v = ⟨z^{G_v}⟩, in the original ambient group. -/
def Uv (z v : G) : Subgroup G := conjugateSpanBy (zpowers z) (Gv v)

theorem z_mem_Uv (z v : G) : z ∈ Uv z v :=
  le_conjugateSpanBy (zpowers z) (Gv v) (mem_zpowers z)

theorem Vv_le_Uv (L : Subgroup G) (z v : G) : Vv L z v ≤ Uv z v :=
  conjugateSpanBy_mono le_rfl (Lv_le_Gv L v)

theorem Uv_le_Gv (z v : G) (hz : z ∈ Gv v) : Uv z v ≤ Gv v :=
  conjugateSpanBy_le_self (zpowers_le.mpr hz)

theorem Gv_normalizes_Uv (z v : G) : Gv v ≤ normalizer (Uv z v : Set G) :=
  le_normalizer_conjugateSpanBy _ _

/-- The genuine conjugation homomorphism on U_v. -/
def uvAction (z v : G) : Gv v →* MulAut (Uv z v) :=
  conjugationAction (Uv z v) (Gv v) (Gv_normalizes_Uv z v)

theorem uvAction_ker (z v : G) :
    (uvAction z v).ker = (centralizer (Uv z v : Set G)).subgroupOf (Gv v) :=
  conjugationAction_ker _ _ _

/-- G*_v = G_v/C_{G_v}(U_v), using the kernel proved above. -/
def Gstar (z v : G) := Gv v ⧸ (uvAction z v).ker
instance (z v : G) : Group (Gstar z v) :=
  inferInstanceAs (Group (Gv v ⧸ (uvAction z v).ker))
instance [Finite G] (z v : G) : Finite (Gstar z v) :=
  inferInstanceAs (Finite (Gv v ⧸ (uvAction z v).ker))

def starMk (z v : G) : Gv v →* Gstar z v := QuotientGroup.mk' (uvAction z v).ker

theorem starMk_surjective (z v : G) : Function.Surjective (starMk z v) :=
  QuotientGroup.mk'_surjective _

theorem starMk_ker (z v : G) :
    (starMk z v).ker = (centralizer (Uv z v : Set G)).subgroupOf (Gv v) := by
  exact (QuotientGroup.ker_mk' (uvAction z v).ker).trans (uvAction_ker z v)

/-- The quotient acts by the actual induced automorphisms. -/
def starAction (z v : G) : Gstar z v →* MulAut (Uv z v) :=
  QuotientGroup.kerLift (uvAction z v)

theorem starAction_injective (z v : G) : Function.Injective (starAction z v) :=
  QuotientGroup.kerLift_injective _

theorem starAction_mk_apply (z v : G) (x : Gv v) (u : Uv z v) :
    ((starAction z v (starMk z v x) u : Uv z v) : G) =
      (x : G) * (u : G) * (x : G)⁻¹ := rfl

/-- The star image of an ambient subgroup, restricted to G_v. -/
def starImage (z v : G) (H : Subgroup G) : Subgroup (Gstar z v) :=
  (H.subgroupOf (Gv v)).map (starMk z v)

/-- The ambient preimage of a subgroup in G*_v. -/
def starPreimage (z v : G) (X : Subgroup (Gstar z v)) : Subgroup G :=
  (X.comap (starMk z v)).map (Gv v).subtype

theorem starPreimage_le_Gv (z v : G) (X : Subgroup (Gstar z v)) :
    starPreimage z v X ≤ Gv v := map_subtype_le _

theorem starImage_starPreimage (z v : G) (X : Subgroup (Gstar z v)) :
    starImage z v (starPreimage z v X) = X := by
  unfold starImage starPreimage
  change (((X.comap (starMk z v)).map (Gv v).subtype).comap (Gv v).subtype).map (starMk z v) = X
  rw [comap_map_eq_self_of_injective (Gv v).subtype_injective,
    map_comap_eq_self_of_surjective (starMk_surjective z v)]

def X0 (L T : Subgroup G) (z v : G) : Set (Subgroup (Gstar z v)) :=
  {X | starImage z v (Lv L v) ⊔ starImage z v (Tv T v) ≤ normalizer (X : Set _) ∧
    (pResidual 2 X).map X.subtype = X ∧ X ≠ ⊥ ∧
    ⁅X, starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ = X}

def XFamily (L T : Subgroup G) (z v : G) : Set (Subgroup (Gstar z v)) :=
  {X | X ∈ X0 L T z v ∧ X.Normal}

/-- The moving condition is expressed through the actual action preimage. -/
def Xz (L T : Subgroup G) (z v : G) : Set (Subgroup (Gstar z v)) :=
  {X | X ∈ X0 L T z v ∧ ¬ starPreimage z v X ≤ centralizer ({z} : Set G)}

/-- U_X = [⟨z^{X* L*_v}⟩,X*], written in the original module subgroup. -/
def UX (L : Subgroup G) (z v : G) (X : Subgroup (Gstar z v)) : Subgroup G :=
  ⁅conjugateSpanBy (zpowers z) (starPreimage z v X ⊔ Lv L v), starPreimage z v X⁆

/-- The family in the paragraph after 13.6.13. -/
def Yz (L T : Subgroup G) (z v : G) : Set (Subgroup G) :=
  {K | K ∈ Chapter1.LIn (Gv v) (Tv T v) ∧
    Theory.GroupTheory.IsQuasisimple (starImage z v K ⧸ pCore 2 (starImage z v K)) ∧
    conjugateSpanBy (starImage z v K) (starImage z v (Tv T v)) ∈ Xz L T z v}

/-- The T_v-conjugate span of K. -/
def Kminus (K T : Subgroup G) (v : G) : Subgroup G := conjugateSpanBy K (Tv T v)

/-- W_K = ⟨z^{K₋L_v}⟩. -/
def WK (K L T : Subgroup G) (z v : G) : Subgroup G :=
  conjugateSpanBy (zpowers z) (Kminus K T v ⊔ Lv L v)

/-- The acting group before taking the plus quotient. -/
def plusActor (K L T : Subgroup G) (v : G) : Subgroup G :=
  Kminus K T v ⊔ Lv L v ⊔ Tv T v

theorem Kminus_le_Gv (K T : Subgroup G) (v : G) (hK : K ≤ Gv v) :
    Kminus K T v ≤ Gv v :=
  conjugateSpanBy_le hK (inf_le_right.trans (Gv v).le_normalizer)

theorem WK_le_Uv (K L T : Subgroup G) (z v : G) (hK : K ≤ Gv v) :
    WK K L T z v ≤ Uv z v :=
  conjugateSpanBy_mono le_rfl (sup_le (Kminus_le_Gv K T v hK) (Lv_le_Gv L v))

theorem Vv_le_WK (K L T : Subgroup G) (z v : G) : Vv L z v ≤ WK K L T z v :=
  conjugateSpanBy_mono le_rfl le_sup_right

/-- An actor preserving both the seed and conjugators preserves their span. -/
theorem normalizes_conjugateSpanBy (Z H A : Subgroup G)
    (hZ : A ≤ normalizer (Z : Set G)) (hH : A ≤ normalizer (H : Set G)) :
    A ≤ normalizer (conjugateSpanBy Z H : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro a ha x ⟨h, hh, z, hz, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨a * h * a⁻¹, (mem_normalizer_iff.mp (hH ha) h).mp hh,
    a * z * a⁻¹, (mem_normalizer_iff.mp (hZ ha) z).mp hz, ?_⟩
  group

/-- The plus action exists because T_v normalizes L_v and fixes z. -/
theorem plusActor_normalizes_WK (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    plusActor K L T v ≤ normalizer (WK K L T z v : Set G) := by
  apply sup_le (le_normalizer_conjugateSpanBy _ _)
  apply normalizes_conjugateSpanBy
  · have he : centralizer ({z} : Set G) = centralizer (zpowers z : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure]
    exact (hz.trans he.le).trans (Subgroup.centralizer_le_normalizer _)
  · intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_sup, Kminus,
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy K (Tv T v) ht),
      mem_normalizer_iff_map_conj_eq.mp (hL ht)]

/-- The action before the plus quotient, with its source normalization inputs. -/
def plusConjugation (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    plusActor K L T v →* MulAut (WK K L T z v) :=
  conjugationAction _ _ (plusActor_normalizes_WK K L T z v hL hz)

theorem plusConjugation_ker (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    (plusConjugation K L T z v hL hz).ker =
      (centralizer (WK K L T z v : Set G)).subgroupOf (plusActor K L T v) :=
  conjugationAction_ker _ _ _

/-- (K₋L_vT_v)⁺ is the faithful action quotient on W_K. -/
def Gplus (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :=
  plusActor K L T v ⧸ (plusConjugation K L T z v hL hz).ker

instance (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) : Group (Gplus K L T z v hL hz) :=
  inferInstanceAs (Group (plusActor K L T v ⧸ (plusConjugation K L T z v hL hz).ker))

instance [Finite G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) : Finite (Gplus K L T z v hL hz) :=
  inferInstanceAs (Finite (plusActor K L T v ⧸ (plusConjugation K L T z v hL hz).ker))

def plusMk (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    plusActor K L T v →* Gplus K L T z v hL hz := QuotientGroup.mk' _

def plusAction (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    Gplus K L T z v hL hz →* MulAut (WK K L T z v) :=
  QuotientGroup.kerLift (plusConjugation K L T z v hL hz)

theorem plusAction_injective (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    Function.Injective (plusAction K L T z v hL hz) := QuotientGroup.kerLift_injective _

theorem plusAction_mk_apply (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (x : plusActor K L T v) (w : WK K L T z v) :
    ((plusAction K L T z v hL hz (plusMk K L T z v hL hz x) w : WK K L T z v) : G) =
      (x : G) * (w : G) * (x : G)⁻¹ := rfl

def plusImage (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) (H : Subgroup G) :
    Subgroup (Gplus K L T z v hL hz) :=
  (H.subgroupOf (plusActor K L T v)).map (plusMk K L T z v hL hz)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
end
