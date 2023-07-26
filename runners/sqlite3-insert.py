import sqlite3
conn = sqlite3.connect('test.db')
c = conn.cursor()
print ("successopen")

c.execute("INSERT INTO wtune_stmts (stmt_app_name, stmt_id, stmt_raw_sql, stmt_trace) \
VALUES ('lobsters', 139, 'select t.id , count ( distinct t.user_id ) from ( select id , user_id from invitations union ( select distinct * from ( select id , user_id from invitations union select id , user_id from invitations ) as t0 ) ) as t group by t.id', '')")

conn.commit()
print ("success insert")
conn.close()