(*  Title:      Stark/Channel_Instances.thy
    Author:     Diego Marmsoler
    Maintainer: Diego Marmsoler
    License:    BSD-3-Clause
*)

theory Channel_Instances
  imports Channel_Transcript
begin

subsection \<open>Boolean Interpretation\<close>

global_interpretation test_channel:
  channel concat_bool
  defines test_send = test_channel.send
      and test_send2 = test_channel.send2
      and test_read = test_channel.read
  .

value "execute (receive_random_field_element) \<lparr>HashMap = (fmempty::(bool, bool) fmap), State = True, Transcript=[]\<rparr>"

value "execute (test_send True) \<lparr>HashMap = (fmempty::(bool, bool) fmap), State = True, Transcript=[]\<rparr>"

text \<open>
  The idea is that if we process a transcript then we recover the state and get the same random element.
  To this end we need to execute the monad on the final HashMap, the initial state and the reversed transcript.
  Each read then modifies the state in the same way as a send which leads to the same result for the hash value
  used to create the random value.
\<close>

value
  "execute (
    do {
      test_send True;
      r1 \<leftarrow> receive_random_field_element;
      test_send False;
      r2 \<leftarrow> receive_random_field_element;
      return r1
    }) \<lparr>HashMap = (fmempty::(bool, bool) fmap), State = True, Transcript=[]\<rparr>"

lemma
  "execute (
    do {
      test_read;
      r1 \<leftarrow> receive_random_field_element;
      test_read;
      r2 \<leftarrow> receive_random_field_element;
      return (r1 \<and> \<not> r2)
    }) \<lparr>HashMap = fmap_of_list [(True, True), (False, False)], State = True, Transcript = rev [False, True]\<rparr>
=
dist_of_fset ({|(Some (True, \<lparr>HashMap = fmap_of_list [(True, True), (False, False)], State = False, Transcript = []\<rparr>), 1)|})"
  by eval

lemma
  "execute (
    do {
      test_read;
      r1 \<leftarrow> receive_random_field_element;
      test_read;
      r2 \<leftarrow> receive_random_field_element;
      return (r1 \<and> r2)
    }) \<lparr>HashMap = fmap_of_list [(True, True), (False, True)], State = True, Transcript = rev [False, True]\<rparr>
=
dist_of_fset ({|(Some (True, \<lparr>HashMap = fmap_of_list [(True, True), (False, True)], State = False, Transcript = []\<rparr>), 1)|})"
  by eval

lemma
  "execute (
    do {
      test_read;
      r1 \<leftarrow> receive_random_field_element;
      test_read;
      r2 \<leftarrow> receive_random_field_element;
      return (\<not> r1 \<and> r2)
    }) \<lparr>HashMap = fmap_of_list [(True, False), (False, True)], State = True, Transcript = rev [False, True]\<rparr>
=
dist_of_fset ({|(Some (True, \<lparr>HashMap = fmap_of_list [(True, False), (False, True)], State = False, Transcript = []\<rparr>), 1)|})"
  by eval

lemma
  "execute (
    do {
      test_read;
      r1 \<leftarrow> receive_random_field_element;
      test_read;
      r2 \<leftarrow> receive_random_field_element;
      return (\<not> r1 \<and> \<not> r2)
    }) \<lparr>HashMap = fmap_of_list [(True, False), (False, False)], State = True, Transcript = rev [False, True]\<rparr>
=
dist_of_fset ({|(Some (True, \<lparr>HashMap = fmap_of_list [(True, False), (False, False)], State = False, Transcript = []\<rparr>), 1)|})"
  by eval

subsection \<open>GF5 Interpretation\<close>

global_interpretation gf5_channel:
  channel concat_gf5
  defines gf5_send = gf5_channel.send
      and gf5_send2 = gf5_channel.send2
      and gf5_read = gf5_channel.read
  .

lemma "execute (receive_random_field_element) \<lparr>HashMap = (fmempty::(gf5, gf5) fmap), State = 0, Transcript=[]\<rparr>
=
dist_of_fset (
    {|(Some (4, \<lparr>HashMap = fmap_of_list [(0, 4)], State = 0, Transcript = []\<rparr>), (1 / 5)),
     (Some (3, \<lparr>HashMap = fmap_of_list [(0, 3)], State = 0, Transcript = []\<rparr>), (1 / 5)),
     (Some (2, \<lparr>HashMap = fmap_of_list [(0, 2)], State = 0, Transcript = []\<rparr>), (1 / 5)),
     (Some (1, \<lparr>HashMap = fmap_of_list [(0, 1)], State = 0, Transcript = []\<rparr>), (1 / 5)),
     (Some (0, \<lparr>HashMap = fmap_of_list [(0, 0)], State = 0, Transcript = []\<rparr>), (1 / 5))|})"
  by eval

lemma "execute (gf5_send 1) \<lparr>HashMap = (fmempty::(gf5, gf5) fmap), State = 0, Transcript=[]\<rparr>
=
dist_of_fset ({|(Some ((), \<lparr>HashMap = fmap_of_list [], State = 1, Transcript = [1]\<rparr>), 1)|})"
  by eval

end
