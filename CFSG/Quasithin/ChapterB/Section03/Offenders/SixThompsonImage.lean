module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixHyperplaneEscape
public import CFSG.Quasithin.ChapterB.Section02.Thompson.HalfImage
public import Theory.GroupTheory.ElementaryThompsonSmallImage

/-!
# The large-image exclusion preceding the six-letter trichotomy

If J₁'s actual image stays in the plane radical, every maximum elementary
image has order at most two. A larger image would have a half-order subgroup
with an even conjugate escaping that radical. The full kernel localization
places this conjugate in J₁'s image, a contradiction. The same marking is
used for the actual Sylow image, the alternating subgroup and the radical.
The original linear short-block consumer is in Amalgam.LinearShortThompson.
This is the image step of 13.2.2(10), not its pushing-up/block conclusion.
Source: Aschbacher–Smith 13.2.2(10), printed p.878.
-/

public noncomputable section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB
open Offenders Offenders.Six
variable {G : Type*} [Group G] [Finite G]

theorem maximum_image_le_two_of_thompson_one_image_le_D
    (T : Sylow 2 G) (q : G →* Perm) (hr : 1 < twoRank (T : Subgroup G))
    (hY : alternatingGroup (Fin 6) ≤ q.range)
    (hT : (T : Subgroup G).map q = sylowCarrier ⊓ q.range)
    (hJ : (thompsonJ (T : Subgroup G) 1).map q ≤ D 6)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G)) :
    Nat.card (A.map q) ≤ 2 := by
  by_contra! hc
  have hAT : A.map q ≤ sylowCarrier := (map_mono hA.1).trans (hT.le.trans inf_le_left)
  obtain ⟨C,hCA,hC,g,hCT,hn⟩ := exists_half_conjugate_escape (A.map q) hAT hc
  have hg : g.val ∈ q.range := hY g.property
  have hCY : C.map (MulAut.conj g.val).toMonoidHom ≤ q.range := by
    rintro _ ⟨c,hc,rfl⟩
    exact mul_mem (mul_mem hg (map_le_range q A (hCA hc))) (inv_mem hg)
  exact hn ((maximum_half_image_conjugate_le_thompson_one T q hr A hA C hCA hC
    g.val hg (hT.symm ▸ le_inf hCT hCY)).trans hJ)

end CFSG.Quasithin.ChapterB
